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
//! holes, empty and not proved so) and `l01_23_groups_and_refusals::refusals::each_refusal_names_its_cause`
//! (`box_cover`). COMPLEXITY.md rows K1 and K2, and the Kept row
//! "emptiness and subtyping of tuple and morphism parts".
//! A complete solution would split the box in every component (a DPLL search over the tuple
//! types, exponential in them), or hand the part to a SAT solver.
//!
//! A query goes in this order, each step a function of the query alone: the simulation proves
//! `a <: b` for unions written without negation; a value built from the rows as written shows a
//! type inhabited; the residue rule speaks for pure cycles; a union of rows is empty row by row;
//! the search decides the rest. The search stops at a fork, two rows open on one box that differ
//! in a recursive column, or two rows taken out of one column with different recursive types
//! there, each on a cycle of its group: `Type::verdict` then seeks a value without following
//! the fork and, finding none, answers `Refused(Fork)`, and `is_empty` counts the type as
//! inhabited. Following the fork is the subset construction, exponential in the recursive types.
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
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::future::Future;
use std::ops::{ControlFlow, Range};
use std::pin::Pin;
use std::sync::{Arc, Mutex};

use num_bigint::{BigInt, BigUint};

use super::bdd::{Bdd, Form, Part};
use super::bes::{Answer, Bes, Decision, Kind, decide};
use super::rec::unfold::eval;
use super::rec::{self, Env, Judgment, Why};
use super::{
    Filer, Held, Lits, Morphism, Node, Parts, PartsRef, Reading, Refusal, Row, RowIndex, Split,
    Tuples, Type, Universes, Verdict, blind, makeable,
};
use crate::digest::{DigestMap, DigestSet};
use crate::frames::{Deep, Stack};
use crate::value::Value;
use shared::{ByType, ChainHint, ChainPlan, Digests, Literal2, TwoSat, list_step, only_atoms};

/// The numbers of the types of a search, one number for the types equal but for definition
/// names ([`blind`]): two renamed copies of a group, and two types that hold them, have one
/// answer, since no rule of the search reads a definition's name, so the search decides them once
/// and its verdicts do not depend on which copy it met first.
// Complexity tradeoff: keyed by both digests (`ByType`), each of k renamed copies of a group
// live in one search is decided apart, down to its own nodes: k times the work of one (seed 32
// of the harness, item GSX-unsolved, I7.3-Opus). Used: a map by the name-free digest, where a
// type is compared with the keys of its digest with names left out, O(1) where the digests
// differ and linear in the size of the two types where they tie. Given up: a copy met again is
// compared in full with the first copy each time, and a collision of the name-free digest
// leaves a list whose keys are compared one by one, O(b) comparisons for b keys.
#[derive(Default)]
struct Ids(HashMap<u64, Vec<(Type, usize)>, Digests>);

impl Ids {
    fn get(&self, t: &Type) -> Option<&usize> {
        let keys = self.0.get(&t.digest())?;
        blind(|| keys.iter().find(|(k, _)| k == t)).map(|(_, i)| i)
    }

    fn insert(&mut self, t: Type, i: usize) {
        let keys = self.0.entry(t.digest()).or_default();
        match blind(|| keys.iter().position(|(k, _)| *k == t)) {
            Some(j) => keys[j].1 = i,
            None => keys.push((t, i)),
        }
    }

    fn remove(&mut self, t: &Type) {
        let d = t.digest();
        let Some(keys) = self.0.get_mut(&d) else {
            return;
        };
        blind(|| keys.retain(|(k, _)| k != t));
        if keys.is_empty() {
            self.0.remove(&d);
        }
    }
}

// Complexity tradeoff: scanning b records at q dependency queries costs O(q*b)
// even when none is a fork. Maintain their count, O(1) per query and insertion;
// removals and compaction charge their work to existing log mutations. Nothing
// is given up: the count is exact. Test: setop::canonical_blame_settlement_scales
// and the Fork diagnostics in refusals; a repeated-query control fails scaling.
/// Refusal records with the number of forks maintained by the same mutations.
/// Testing whether a fork exists is constant time; scanning records at every
/// dependency query otherwise multiplies the queries by the accumulated records.
#[derive(Default)]
struct Blames {
    entries: Vec<(usize, Refusal, usize)>,
    forks: usize,
}

impl std::ops::Deref for Blames {
    type Target = [(usize, Refusal, usize)];
    fn deref(&self) -> &Self::Target {
        &self.entries
    }
}

impl Blames {
    fn push(&mut self, entry: (usize, Refusal, usize)) {
        self.forks += usize::from(entry.1 == Refusal::Fork);
        self.entries.push(entry);
    }

    fn extend(&mut self, entries: impl IntoIterator<Item = (usize, Refusal, usize)>) {
        for entry in entries {
            self.push(entry);
        }
    }

    fn retain(&mut self, mut keep: impl FnMut(&(usize, Refusal, usize)) -> bool) {
        self.entries.retain(|entry| {
            if keep(entry) {
                true
            } else {
                self.forks -= usize::from(entry.1 == Refusal::Fork);
                false
            }
        });
    }

    fn truncate(&mut self, len: usize) {
        for entry in self.entries.get(len..).unwrap_or_default() {
            self.forks -= usize::from(entry.1 == Refusal::Fork);
        }
        self.entries.truncate(len);
    }

    fn copy_entry(&mut self, to: usize, from: usize) {
        let entry = self.entries[from];
        self.forks -= usize::from(self.entries[to].1 == Refusal::Fork);
        self.forks += usize::from(entry.1 == Refusal::Fork);
        self.entries[to] = entry;
    }
}

/// A set of types, hashed by their digests.
type TypeSet = HashSet<Type, Digests>;
/// The reads and blame a proof resting on a fork added for the type being decided, taken out
/// by [`Searching::take_fork`] and put back by [`Searching::restore_fork`].
type ForkSave = (Vec<usize>, Vec<(usize, Refusal)>);

thread_local! {
    static MEMO: RefCell<ByType<bool>> = const { RefCell::new(ByType::new()) };
    /// The answer of [`Type::empty_past_forks`] for each type asked: a function of the type alone.
    static PAST_FORKS: RefCell<ByType<bool>> =
        const { RefCell::new(ByType::new()) };
    /// The bounds on the heights of the values of each type asked ([`height_bounds`]): a
    /// function of the type alone, kept for every search until `Type::forget_emptiness`.
    ///
    /// Proof that a kept entry is never stale, so no change needs to drop it
    /// (TEST-heights-cache-invalidation): (1) a type never changes: `Type` is an `Arc` of a
    /// node no method changes once built; a recursive node sets lazily only its name, its atom
    /// names and its unfolding, and the unfolding is `make()` of its key, the same parts each
    /// time `rec::unfold::end_unit` drops it and a use makes it again. (2) The map finds an
    /// entry only for a type equal to the one asked (`Eq` on `Type`): two nodes of parts are
    /// equal only when their parts are, child by child, and two recursive nodes only when their
    /// keys name one class of one canonical form at equal arguments (`rec::Key::order`), whose
    /// unfoldings are the same parts over equal children. (3) `Heights::height_bounds`,
    /// `least_height` and `most_height` read nothing but the parts of the type asked and of the
    /// types it reaches (`Type::p`) and the entries of the same maps, so by induction on the
    /// order in which entries are made each entry is what a fresh `Heights` finds for every type
    /// equal to its key. The proof rests on (2) for recursive nodes of two instances that the
    /// canonical form merges; the test
    /// `types::empty::tests::kept_height_bounds_agree_with_fresh_ones_across_rebuilds` builds
    /// such instances again from the same draws, and compares the kept bounds with fresh ones
    /// before and after `forget_emptiness`, with a wrong entry as its negative control.
    static HEIGHTS: RefCell<Heights> = RefCell::new(Heights::default());
    /// The verdict of each type asked. A verdict is decided by a search that reads no kept
    /// result, or with the other members of its recursive group ([`group_verdicts`]), so it is
    /// a function of the type alone, and keeping it changes no answer: these
    /// are the types proved empty and those with a checked value, and the refusals.
    static VERDICTS: RefCell<ByType<Verdict>> =
        const { RefCell::new(ByType::new()) };
    /// The members of the groups whose verdicts are being decided ([`group_verdicts`]): a search
    /// decides such a member itself, where it reads the verdict of any other member.
    static DECIDING: RefCell<TypeSet> = const { RefCell::new(TypeSet::with_hasher(Digests::new())) };
    /// The values the searches of [`group_verdicts`] built, one list per search, each value by
    /// its number there, as [`Search::shown`] holds them: read, never changed, by the searches
    /// that read a member's value ([`Rep::Of`]), until `Type::forget_emptiness`.
    // Complexity tradeoff: every value a group's searches built is kept until the unit ends,
    // those no reader reads too, so the memory is that of every group's searches together,
    // O(total values built), where a search's values were dropped when it ended; it buys reads
    // with no copy. Trigger: any group decided by `group_verdicts`. COMPLEXITY.md K62.
    // Naive version (K62): a reader outside the group gets a search of its own that reads no
    // kept value, deciding again the part of the group it reaches, O(m·n) for m readers of a
    // group of n; used: the kept values read by index, O(1) per read.
    static STORES: RefCell<Vec<Vec<Rep>>> = const { RefCell::new(Vec::new()) };
    /// The classes of the values in `STORES` ([`stored_class`]).
    static CLASSES: RefCell<Classes> = RefCell::new(Classes::default());
    /// For each member given `Inhabited` by [`group_verdicts`] with a value its searches built:
    /// the list in `STORES` and the value's number there.
    static SHARED: RefCell<ByType<(usize, usize)>> =
        const { RefCell::new(ByType::new()) };
    /// The members of recursive groups this thread sent to the search of [`group_verdicts`]
    /// because their group's decider left them open ([`Type::members_searched`]).
    static SEARCHED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// Whether `Searching::nested_cover` is skipped, so that a box goes from the split into
    /// disjoint parts to `Searching::take_out_piece` and the split into the open tuple types:
    /// set only by [`Type::without_nested_cover`], for the test that compares the two paths.
    static NO_NESTED_COVER: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// Whether `Searching::nested_pieces` also cuts the pieces one cell at a time, checks that
    /// they are the pieces `Searching::laminar_pieces` finds whenever it decides them, and
    /// answers with them: set only by [`Type::with_pieces_compared`], for the test of the cut
    /// one cell at a time, which product code takes only after a test not decided.
    static PIECES_COMPARED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Keeps the verdicts of `members`, the recursive members of one group. A member the group's
/// decider (module `bes`) decides empty is `Empty`, and one it decides inhabited is `Inhabited`
/// once a value of it is built and checked. The members it does not decide are decided by one
/// search with all of them as roots ([`Search::solve_all`]), as [`Type::verdict_alone`] decides
/// one: a member is `Empty` when the search proves it so and no fork lies under it, and
/// `Inhabited` when a value of it is built, by that search or by the search for values below.
/// Values are built by one search for all members, in definition order, which keeps each value
/// it builds, so a type shared by members is given its value once. So the verdicts of a group of
/// n cost what one search over the group does, where a search for each member would read the
/// group n times. Each verdict is a function of the group, which every member names,
/// whichever member is asked first.
fn group_verdicts(members: &[Type]) {
    DECIDING.with(|d| d.borrow_mut().extend(members.iter().cloned()));
    let order: Vec<usize> = (0..members.len()).collect();
    let open: Vec<Type> = order
        .iter()
        .map(|&i| &members[i])
        .filter(|m| m.judged().is_none())
        .cloned()
        .collect();
    SEARCHED.with(|c| c.set(c.get() + open.len()));
    let mut d = Search {
        strict: true,
        refuse_forks: true,
        is_group: true,
        blame: Some(Blames::default()),
        ..Search::default()
    };
    let answers = d.solve_all(&open);
    let causes = d.causes();
    // For each member not decided by the decider, in order: whether the search proved it
    // empty, its number there, and the cause its answer may rest on. A fork met with no type
    // being decided ends the search, and refuses every root, as it does for one.
    let mut found = (open.iter().zip(answers))
        .map(|(m, b)| {
            let id = d.ids.get(m).copied();
            (b, id, d.refused.or(id.and_then(|i| causes[i])))
        })
        .collect::<Vec<_>>()
        .into_iter();
    // The search for values does not stop at a fork, as the one before a refusal in
    // [`Type::verdict_alone`] does not.
    let mut s = Search {
        strict: true,
        open_forks: true,
        ..Search::default()
    };
    // The search in which each closure is taken to have a value, run only for a member that
    // would be refused, and `None` inside when it showed no values.
    let mut o: Option<Option<Search>> = None;
    let mut horn_tried = members.iter().any(|m| m.judged() == Some(false))
        && members.first().is_some_and(|first| {
            let Node::Rec(r) = &*first.0 else {
                return false;
            };
            r.key
                .member_at()
                .is_some_and(|(env, _)| group_has_diff_or_and(env))
        });
    if horn_tried {
        horn_witness_group(members, &mut s);
    }
    let mut undecided = Vec::new();
    for &i in &order {
        let m = &members[i];
        let v = match m.judged() {
            Some(true) => Verdict::Empty,
            Some(false) if s.rep(m).is_some() => Verdict::Inhabited,
            // Complexity tradeoff: groups in `C_group` with `&` or `\` already ran
            // `horn_witness_group` once above in `O(S + n*k)` time (Dowling & Gallier 1984
            // event-driven Horn propagation, without materializing plain height-`n` `Value`s in
            // `Type::contains_kept`), avoiding `O(n²)` per-member `find_rep` searches on wide
            // tuple differences (`xr_r2_bench_cgroup_long_tuples_and_many_diffs_scales`); only a
            // member outside `C_group` whose value the shared search did not build falls back to
            // a search of its own (COMPLEXITY.md K56).
            Some(false) => {
                if !horn_tried {
                    horn_tried = true;
                    horn_witness_group(members, &mut s);
                }
                if s.reps.get(m).is_some_and(Option::is_some) {
                    Verdict::Inhabited
                } else {
                    m.verdict_alone()
                }
            }
            None => {
                let (b, id, cause) = found.next().expect("one answer per member not decided");
                let decided = cause != Some(Refusal::Fork);
                if decided && b {
                    Verdict::Empty
                } else if (d.refused.is_none() && id.is_some_and(|i| d.witnessed.contains(&i)))
                    || (decided && d.rep(m).is_some())
                    || s.rep(m).is_some()
                    || (o.get_or_insert_with(|| optimistic_values(members)).as_mut())
                        .is_some_and(|o| o.rep(m).is_some())
                {
                    Verdict::Inhabited
                } else if m.refused_by_group() {
                    // Complexity tradeoff at `Type::verdict_alone`: neither proved empty nor
                    // shown inhabited, so refused. A member the group's decider refused is
                    // refused for that, whatever stopped the search, so that its message names
                    // the definitions, the cycles and the tuple behind it (`Type::refusal_site`).
                    // Complexity tradeoff: such a member counts as inhabited, `Refusal::Group`.
                    // Why: its component, with two or more independent cycles mixing tuples and
                    // function results and a tuple with two undecided components (module `bes`,
                    // step 5), is a game the known algorithms solve in time quadratic in the
                    // group, and the decider stays linear; the member goes to the search, as
                    // DESIGN.md L1.23 has every member the decider refuses, which decides some.
                    // Trigger: `Answer::Refused` for the member in either run of `judge`, and the
                    // search deciding nothing. Tests: `l01_23_subtyping::group_refusal`.
                    // COMPLEXITY.md K85. A complete solution needs a game solver quadratic in
                    // the component.
                    Verdict::Refused(Refusal::Group)
                } else {
                    undecided.push(m.clone());
                    Verdict::Refused(cause.or(d.gave_up).unwrap_or(Refusal::NoWitness))
                }
            }
        };
        VERDICTS.with(|k| k.borrow_mut().insert(m.clone(), v));
    }
    // The values built here, kept for the searches that read a member ([`Searching::shared`]):
    // a member shown inhabited by a value of the search for values, else of the first search,
    // else of the search in which each closure was taken to have a value.
    let mut o = o.flatten();
    if !undecided.is_empty() {
        for t in 0..d.types.len() {
            if s.reps.get(&d.types[t]).is_some_and(Option::is_some) {
                d.witnessed.insert(t);
            }
        }
    }
    STORES.with(|st| {
        let mut st = st.borrow_mut();
        let (first, values, taken) = (st.len(), st.len() + 1, st.len() + 2);
        SHARED.with(|sh| {
            let mut sh = sh.borrow_mut();
            for m in members {
                if VERDICTS.with(|k| k.borrow().get(m) != Some(&Verdict::Inhabited)) {
                    continue;
                }
                if let Some(Some(r)) = s.reps.get(m) {
                    sh.insert(m.clone(), (values, *r));
                } else if let Some(Some(r)) = d.reps.get(m) {
                    sh.insert(m.clone(), (first, *r));
                } else if let Some(Some(r)) = o.as_ref().and_then(|o| o.reps.get(m)) {
                    sh.insert(m.clone(), (taken, *r));
                }
            }
        });
        st.push(std::mem::take(&mut d.shown));
        st.push(std::mem::take(&mut s.shown));
        if let Some(o) = o.as_mut() {
            st.push(std::mem::take(&mut o.shown));
        }
    });
    if !undecided.is_empty() {
        DECIDING.with(|dec| {
            let mut dec = dec.borrow_mut();
            for m in members {
                if !undecided.contains(m) {
                    dec.remove(m);
                }
            }
        });
        for m in members {
            if VERDICTS.with(|k| k.borrow().get(m) == Some(&Verdict::Inhabited))
                && let Some(&id) = d.ids.get(m)
            {
                d.witnessed.insert(id);
                d.blamed_node[id] = false;
            }
        }
        d.settle_canonical_blame(&undecided);
        let c_causes = d.causes();
        VERDICTS.with(|k| {
            let mut k = k.borrow_mut();
            for m in &undecided {
                let id = d.ids.get(m).copied();
                // The reason, by a fixed priority over what this search recorded: the refusal
                // that ended the search, else the cause the member's answer rests on
                // (`Search::causes`), else the give-up first in `refusal_rank`, else
                // NoWitness. It is a function of the group as written, the same in every build
                // and run. It is not a function of the meaning alone: a group written with the
                // operands of `&` or `|` in another order is another type, and one written with
                // its definitions in another order is searched from its members in that order;
                // either search may meet the parts in another order and record another cause.
                // In the sweep of 16000 random groups, each in five presentations (plan item
                // GSX-unsolved), three members get two reasons across the presentations of one
                // group (seed 3390: MorphismSplit and NoWitness; 4502: Fork and NoWitness); no
                // verdict changes. Searching the members in digest order moves the difference
                // from 4502 to 5200, so the order of the roots alone does not fix it.
                let r = d
                    .refused
                    .or(id.and_then(|i| c_causes[i]))
                    .or(d.gave_up)
                    .unwrap_or(Refusal::NoWitness);
                k.insert(m.clone(), Verdict::Refused(r));
            }
        });
        refine_tuple_forks(&undecided);
        DECIDING.with(|dec| {
            let mut dec = dec.borrow_mut();
            for m in &undecided {
                dec.remove(m);
            }
        });
    } else {
        DECIDING.with(|dec| {
            let mut dec = dec.borrow_mut();
            for m in members {
                dec.remove(m);
            }
        });
    }
}

/// Tries the exact tuple-universe identities only for settled Fork refusals.
// Complexity tradeoff: leaving `(_, .., _)` as an open atom may create a recursive
// fork that disappears when its known truth is substituted. Try this second proof
// domain once for the refused roots together, each diagram normalized once there.
// Only clean Empty proofs are retained; every other verdict and its settled reason
// stay with the ordinary search. This is a fixed pair of proof domains, not a
// retry budget or a size-dependent decision. Non-Fork refusals need no such proof.
fn refine_tuple_forks(undecided: &[Type]) {
    let roots: Vec<Type> = VERDICTS.with(|v| {
        let v = v.borrow();
        undecided
            .iter()
            .filter(|m| v.get(m) == Some(&Verdict::Refused(Refusal::Fork)))
            .cloned()
            .collect()
    });
    if roots.is_empty() {
        return;
    }
    let mut proof = Search {
        strict: true,
        refuse_forks: true,
        is_group: true,
        blame: Some(Blames::default()),
        tuple_universe: true,
        ..Search::default()
    };
    let empty = proof.solve_all(&roots);
    let causes = proof.causes();
    if proof.refused.is_none() {
        VERDICTS.with(|v| {
            let mut v = v.borrow_mut();
            for (m, empty) in roots.into_iter().zip(empty) {
                if empty
                    && proof
                        .ids
                        .get(&m)
                        .is_none_or(|&id| causes[id] != Some(Refusal::Fork))
                {
                    v.insert(m, Verdict::Empty);
                }
            }
        });
    }
}

/// The search for values of `members` in which each closure whose keys are permitted as written
/// is taken to have a value at once, its value type put on a list; kept only when each type on
/// the list then has a value built in this same search, and `None` when one has none. The
/// closures taken then each return a value built of the closures taken, so every value it built
/// is a value: a function may return a value that holds it. It shows a value where the search
/// that takes a closure only once its value type has a value ([`Searching::find_rep`]) met the
/// types in an order that left a value type without one while it was being built
/// (GROUP-closure-order: x15407 of `group_oracle` needs it in some orders of its definitions).
/// It is not complete: it builds no value of some meets, such as a member and `(top, top)`
/// (GROUP-search-meet-values), and it gives up whole when one closure taken has a value type
/// without a value, even if no member needs that closure. So it does not make the verdicts
/// independent of order where meets are involved. On the 32,300 random groups of the
/// GROUP-closure-order runs, the verdicts that differed between orders were the same with it
/// and without it: x15407 is the only group known to need it.
// Complexity tradeoff: one more search for values over the group, run only when a member would
// otherwise be refused, so a refusal costs up to twice the search it cost before; each value
// type taken is shown to have a value once, read from the kept values after its first build.
// When one has none the search gives up whole rather than dropping that closure and searching
// again, which would decide the group exactly (the game DESIGN.md L1.23 refuses) but in time
// quadratic in it. Trigger: a member of a group the decider refused that the other searches
// build no value of. Tests: `l01_23_groups_and_refusals::group_oracle` (GROUP-closure-order).
fn optimistic_values(members: &[Type]) -> Option<Search> {
    let mut o = Search {
        strict: true,
        open_forks: true,
        optimistic: Some(Vec::new()),
        ..Search::default()
    };
    for i in carrier_root_order(members) {
        o.rep(&members[i]);
    }
    let mut shown = 0;
    while let Some(v) = (o.optimistic.as_ref()).and_then(|vs| vs.get(shown).cloned()) {
        shown += 1;
        o.rep(&v)?;
    }
    Some(o)
}

impl Type {
    /// Drops the kept emptiness results, and ends the unit of the recursive instances this
    /// thread made (`rec::unfold::end_unit`). A unit's checker calls it first: a type equal to
    /// a kept one but built apart from it is compared with it in full, so a result kept from
    /// another unit costs the size of the type at each lookup; and a recursive instance is a
    /// cycle, which only the end of its unit frees once no one holds it.
    pub fn forget_emptiness() {
        super::clear_compound_types();
        MEMO.with(|m| m.borrow_mut().clear());
        PAST_FORKS.with(|m| m.borrow_mut().clear());
        HEIGHTS.take();
        VERDICTS.with(|m| m.borrow_mut().clear());
        STORES.with(|m| m.borrow_mut().clear());
        CLASSES.with(|m| *m.borrow_mut() = Classes::default());
        SHARED.with(|m| m.borrow_mut().clear());
        GROUPS.with(|ms| {
            ms[0].borrow_mut().clear();
            ms[1].borrow_mut().clear();
        });
        super::rec::unfold::end_unit();
    }

    /// How many members of recursive groups this thread has sent to the search because their
    /// group's decider (module `bes`) left them open; a count that only grows, read by the tests
    /// to show which groups the decider settles with no search.
    pub fn members_searched() -> usize {
        SEARCHED.with(std::cell::Cell::get)
    }

    /// Runs `f` with `Searching::nested_cover` skipped, the kept emptiness results dropped
    /// before and after, so no result crosses from one path to the other. For the test that
    /// compares the two paths (TEST-nested-cover-verdict-change).
    #[doc(hidden)]
    pub fn without_nested_cover<R>(f: impl FnOnce() -> R) -> R {
        Type::forget_emptiness();
        NO_NESTED_COVER.with(|c| c.set(true));
        let r = f();
        NO_NESTED_COVER.with(|c| c.set(false));
        Type::forget_emptiness();
        r
    }

    /// Runs `f` with `Searching::nested_pieces` cutting the pieces both ways and checking that
    /// they agree, answering with those cut one cell at a time; the kept emptiness results
    /// dropped before and after. For the test of the cut one cell at a time.
    #[doc(hidden)]
    pub fn with_pieces_compared<R>(f: impl FnOnce() -> R) -> R {
        Type::forget_emptiness();
        PIECES_COMPARED.with(|c| c.set(true));
        let r = f();
        PIECES_COMPARED.with(|c| c.set(false));
        Type::forget_emptiness();
        r
    }

    /// The emptiness the group of a recursive member decides for it, if any ([`judge`]), decided
    /// for every member of its instance when first asked.
    pub(crate) fn judged(&self) -> Option<bool> {
        let Node::Rec(r) = &*self.0 else {
            return None;
        };
        let (env, i) = r.key.member_at()?;
        env.judged.get_or_init(|| judge(env)).answers[i]
    }

    /// Whether `self` is a recursive member that its group's decider refuses ([`judge`]).
    pub(crate) fn refused_by_group(&self) -> bool {
        let Node::Rec(r) = &*self.0 else {
            return false;
        };
        r.key
            .member_at()
            .is_some_and(|(env, i)| env.judged.get_or_init(|| judge(env)).refused[i])
    }

    /// The emptiness that the decider of the recursive group of `self` (module `bes`) gives it,
    /// when `self` is a member that decider decides: `Some(true)` empty, `Some(false)`
    /// inhabited. `None` for any other type, and for a member it refuses or leaves to the
    /// search.
    pub fn decided_by_group(&self) -> Option<bool> {
        self.diagonal_empty()
            .then_some(true)
            .or_else(|| self.judged())
    }

    fn diagonal_empty(&self) -> bool {
        matches!(&*self.0, Node::Rec(r) if r.key.diagonal_empty())
    }

    /// Whether no value is in `self`, as far as the search proves it: a type it does not prove
    /// empty, as one whose search meets a fork, counts as inhabited.
    pub fn is_empty(&self) -> bool {
        if self.diagonal_empty() {
            return true;
        }
        // A type of scalars alone is empty when its parts list none, which costs less than
        // finding the type among those kept.
        if let Node::Parts(p, _) = &*self.0 {
            if p.scalars_only() {
                return !p.has_scalars();
            }
            // A type whose parts list a scalar, a bare atom or the atoms of every name not
            // listed holds that value: it is read from the parts, where a search would build
            // and try a value for each type asked, and keeps none of a root holding atoms
            // (PERF-deep-ops-slow).
            if p.has_scalars() || p.has_bare_atoms() {
                return false;
            }
        }
        if let Some(b) = MEMO.with(|m| m.borrow().get(self).copied()) {
            return b;
        }
        if let Some(v) = sweep::front_sweep(self) {
            let b = v == Verdict::Empty;
            MEMO.with(|m| m.borrow_mut().insert(self.clone(), b));
            return b;
        }
        // Complexity tradeoff: a fork of recursive tuple types (`Searching::narrow_tuples`,
        // `Searching::tuples_on`) ends the search, and `self` counts as inhabited, as for
        // `Type::verdict`, which refuses it. Why: following both tuple types of a fork is the
        // subset construction, exponential in the recursive types (the lists of int against
        // lists with a 1 at each place from the end up to `n`: 8 ms, 277 ms and 32.5 s at `n`
        // 1, 4 and 6 when the search followed it). Trigger: a fork met in the search. Tests:
        // `l01_23_groups_and_refusals::refusals::bench::emptiness_counts_a_fork_as_inhabited_in_its_size`.
        // COMPLEXITY.md K35, K126. A complete solution needs the subset construction over the forked
        // tuple types; deciding whether such a union holds every list is NFA universality,
        // PSPACE-complete. The answers of a search a fork ended may rest on it, so none is kept.
        // Used: the search stopped at the fork, polynomial in the types written (module
        // comment).
        let mut s = Search {
            refuse_forks: true,
            trials: Some(0),
            ..Search::default()
        };
        let b = s.solve(self);
        if s.refused.is_some() {
            // A search that sets the fork aside may still prove `self` empty, by a part the fork
            // is not under ([`Type::empty_past_forks`]), wherever the fork was met: until
            // FAIL-judgments-query-order-seed it ran only for a fork met in a component of a box
            // with components after it, so a fork met before the search reached an empty
            // component left `self` inhabited alone and empty after a query that kept that
            // component empty.
            // Assumption, not proved (ASSUME-documented): that `is_empty` is now a function of
            // the type alone, whatever earlier queries left in `MEMO`. The search above is not
            // `strict`, so it reads `MEMO`; a kept answer can let it finish where a fresh search
            // would meet a fork, and the answer then comes from `MEMO`, not from the strict
            // `empty_past_forks`. Evidence: `order_free` over seeds 0 to 199 in
            // `l01_23_groups_and_refusals::judgments::bench` and the pinned seed
            // 10511391382961984112 in `judgments.rs`. If false, a subtype answer depends on the
            // queries asked before it: no answer is wrong (a type not proved empty counts as
            // inhabited, and every empty answer is a proof), but checking is not deterministic.
            return s.refused == Some(Refusal::Fork) && self.empty_past_forks();
        }
        MEMO.with(|m| {
            m.borrow_mut()
                .extend(s.types.iter().cloned().zip(s.answer.iter().copied()))
        });
        b
    }

    /// `self` split into its values of each base type, its atoms and the rest: what `self & t`
    /// gives for `t` each base type, and then the atoms and the other universes, each made by
    /// copying one part of `self`, where the meets would build each part of each result.
    pub fn split(&self) -> Split {
        let p = self.p();
        let lits = |l: &Lits, set: fn(&mut Parts, Lits)| {
            (l.cofinite || !l.values.is_empty()).then(|| Type::with(|q| set(q, l.clone())))
        };
        let bools = (p.bools != 0).then(|| Type::with(|q| q.bools = p.bools));
        let atoms = (!p.atoms.is_default())
            .then(|| Type::with(|q| q.atoms = p.atoms.clone()))
            .filter(|t| !t.is_empty());
        let rest = (!p.tuples.is_default() || p.structs || p.morphisms.is_leaf() != Some(false))
            .then(|| {
                Type::with(|q| {
                    q.tuples = p.tuples.clone();
                    q.structs = p.structs;
                    q.morphisms = p.morphisms.clone();
                })
            })
            .filter(|t| !t.is_empty());
        Split {
            bases: [
                bools,
                lits(&p.ints, |q, l| q.ints = l),
                lits(&p.rats, |q, l| q.rats = l),
                lits(&p.floats, |q, l| q.floats = l),
                lits(&p.strings, |q, l| q.strings = l),
                lits(&p.f32s, |q, l| q.f32s = l),
            ],
            atoms,
            rest,
        }
    }

    /// Which parts [`Type::split`] gives, read from the parts as it reads them, but with a type
    /// built only for the atoms and for the rest where they are listed, to tell whether they
    /// are empty: the values of the carriers need no type, nor atoms that hold a bare atom (all
    /// the names but those listed, or a listed name with its bare atom), so a type within one
    /// carrier, or of bare atoms, is read with none built.
    pub fn universes(&self) -> Universes {
        let p = self.p();
        let lits = |l: &Lits| l.cofinite || !l.values.is_empty();
        let bare = p.has_bare_atoms();
        let atoms = !p.atoms.is_default()
            && (bare || !Type::with(|q| q.atoms = p.atoms.clone()).is_empty());
        let rest = (!p.tuples.is_default() || p.structs || p.morphisms.is_leaf() != Some(false))
            && !Type::with(|q| {
                q.tuples = p.tuples.clone();
                q.structs = p.structs;
                q.morphisms = p.morphisms.clone();
            })
            .is_empty();
        Universes {
            bases: [
                p.bools != 0,
                lits(&p.ints),
                lits(&p.rats),
                lits(&p.floats),
                lits(&p.strings),
                lits(&p.f32s),
            ],
            atoms,
            rest,
        }
    }

    /// Whether `self` is empty, shown inhabited by a checked value, or refused: not proved
    /// empty, and no value found. Kept results are not read, since those of `is_empty` carry no
    /// value and would make the outcome depend on the queries before it. A member of a recursive
    /// group gets its verdict with the other members (`group_verdicts`), after the groups it
    /// reads. A type outside a group runs first only the deciders of the groups it reads; the
    /// verdict of a group is decided when a search first reads one of its members, so a type
    /// whose search reads no member's verdict or value decides no group: the meet of two cycles
    /// is decided by the rule on residues and reads neither group's values (plan item
    /// VERDICT-meet-cost).
    pub fn verdict(&self) -> Verdict {
        if self.diagonal_empty() {
            return Verdict::Empty;
        }
        let kept = || VERDICTS.with(|m| m.borrow().get(self).copied());
        if let Some(v) = kept() {
            return v;
        }
        let members = self.group_members();
        self.decide_groups_read(members.is_some());
        if let Some(members) = members {
            group_verdicts(&members);
            if let Some(v) = kept() {
                return v;
            }
        }
        // A type outside a group gets a search of its own, which reads each member of a group by
        // the group's verdict and value, kept above (`Searching::group_verdict`,
        // `Searching::shared`), so the verdicts of m types that read a group of n cost one
        // search of the group and one of each type's own part, not m searches of the group.
        // COMPLEXITY.md K62.
        let v = self.verdict_alone();
        VERDICTS.with(|m| m.borrow_mut().insert(self.clone(), v));
        v
    }

    /// Runs the decider (`Type::judged`) of every group of recursive members that `self` reads,
    /// and of those they read, each group after the groups it reads, from a stack on the heap;
    /// with `verdicts`, which a member of a group asks, it keeps their verdicts too. A decider
    /// reads the verdicts of the parts its members read, and a search reads the decider of a
    /// member it meets and the verdict and value of a member of another group
    /// ([`Searching::group_verdict`], [`Searching::shared`]); run here first, what is read is
    /// kept when it is read, so a decider or a search starts inside another at most one level
    /// deep (a search of a type outside a group, and below it the searches of the groups whose
    /// verdicts it reads, which find what they read kept), and a chain of groups each reading
    /// the next is decided with no more of the thread's stack than two. A type outside a group
    /// keeps no group's verdict here: a group whose members its search never reads costs only its
    /// decider, not a search for each member's value (plan item VERDICT-meet-cost). A group is
    /// found by a walk of the parts its members read, which stops at the members of other groups
    /// and notes each group once (`Type::group`); each type is walked once per walk, a group
    /// already kept, or with its decider run when `verdicts` is false, is not walked, and the
    /// others are walked once, so a walk costs no more than the search that reads the same
    /// parts. Groups form no cycle (a group is a set of definitions that read each other), and
    /// the order is the walk's, which is a function of `self`.
    fn decide_groups_read(&self, verdicts: bool) {
        let own = self.group_members().unwrap_or_else(|| vec![self.clone()]);
        let kept = |m: &Type| VERDICTS.with(|k| k.borrow().contains_key(m));
        // One member of each group read by the parts of `roots`, without passing through a
        // member of another group, in the order met.
        let read = |roots: &[Type]| -> Vec<Type> {
            let mut groups: HashSet<u64> = roots.iter().filter_map(Type::group).collect();
            // `inside` and `seen` are keyed by node numbers, which are never reused, so they
            // hold no node; neither is iterated (the groups found are in the order met).
            let inside: HashSet<u64> = roots.iter().map(Type::node_id).collect();
            let mut seen: HashSet<u64, Digests> = roots.iter().map(Type::node_id).collect();
            // Complexity tradeoff (COMPLEXITY.md K102): the naive read scans the diagram of
            // each type it meets afresh, so a diagram shared by n types is read n times,
            // O(n^2) on cycle_dup's family of n meets each written in two orders. Here the
            // diagram nodes, set nodes and types already read are kept in sets for the whole
            // read (`rows`, `morphisms`, `seen`), O(V + E) expected time in the nodes and
            // edges reached and O(V) space. Given up: the sets live for one read, so two
            // reads (two calls of `Type::verdict`) still read a shared diagram once each. No
            // dependency is lost, since a node is skipped only when it was read before.
            // Tests: cycle_dup::shared_parts_are_read_once_when_deciding_their_groups and the
            // tests that a batch and a single query agree.
            let (mut rows, mut morphisms, mut payload_seen) = (
                DigestSet::default(),
                DigestSet::default(),
                DigestSet::default(),
            );
            let mut found = Vec::new();
            let mut stack: Vec<Type> = roots.to_vec();
            let visit = |t: &Type, seen: &mut HashSet<u64, Digests>, stack: &mut Vec<Type>| {
                if seen.insert(t.node_id()) {
                    stack.push(t.clone());
                }
            };
            while let Some(t) = stack.pop() {
                if let Some(g) = t.group().filter(|_| t.is_member())
                    && !inside.contains(&t.node_id())
                {
                    if groups.insert(g) {
                        found.push(t);
                    }
                    continue;
                }
                let p = t.p();
                // Complexity tradeoff (R11-C3): iterating all payload-bearing names of every
                // prefix union sharing one persistent map costs `Theta(n^2 log n)`
                // (`r11_payload_name_prefixes_must_scale`). Visiting each shared `PayloadNode`
                // once via `payload_seen` reduces the walk to `O(V + E)` in the distinct tree
                // nodes reached (`O(n log n)` across `n` prefix unions).
                p.atoms
                    .payload_entries_unseen(&mut payload_seen, &mut |_name, _bare, payload| {
                        visit(payload, &mut seen, &mut stack);
                    });
                for part in p.tuples.lens.values() {
                    part.atoms_unseen(&mut rows, &mut |row| {
                        row.iter().for_each(|x| visit(x, &mut seen, &mut stack));
                        true
                    });
                }
                p.morphisms.atoms_unseen(&mut morphisms, &mut |m| {
                    for x in [&m.guarantee, &m.permission, &m.value] {
                        visit(x, &mut seen, &mut stack);
                    }
                    true
                });
            }
            found
        };
        enum Step {
            /// A member of a group to walk, unless it is kept, being decided or walked.
            Enter(Type),
            /// The members of a group whose read groups are all decided.
            Leave(Vec<Type>),
        }
        let mut done: HashSet<u64> = own.iter().filter_map(Type::group).collect();
        let mut stack: Vec<Step> = (read(&own).into_iter().rev()).map(Step::Enter).collect();
        while let Some(step) = stack.pop() {
            match step {
                Step::Leave(g) if verdicts => {
                    if !kept(&g[0]) {
                        group_verdicts(&g);
                    }
                }
                Step::Leave(g) => {
                    g[0].judged();
                }
                Step::Enter(m) => {
                    let deciding = || DECIDING.with(|d| d.borrow().contains(&m));
                    let fresh = m.group().is_some_and(|g| done.insert(g));
                    if !fresh || kept(&m) || deciding() || !verdicts && m.judged_known() {
                        continue;
                    }
                    let g = m.group_members().unwrap_or_default();
                    if g.is_empty() {
                        continue;
                    }
                    let reads = read(&g);
                    stack.push(Step::Leave(g));
                    stack.extend(reads.into_iter().rev().map(Step::Enter));
                }
            }
        }
    }

    /// The verdict of `self` by the front sweep (`sweep::front_sweep`), else by the
    /// prefix-chain sweep (`Searching::sweep_verdict`); `None` when `self` is outside both
    /// classes or both leave it to the search. For tests, which check it against an oracle of
    /// their own.
    pub fn sweep_verdict(&self) -> Option<Verdict> {
        sweep::front_sweep(self).or_else(|| self.chain_verdict())
    }

    /// Diagnostic counts of cell reads and of empty cells among them in the independent escape
    /// parse (see `escape::cell_counts`).
    #[doc(hidden)]
    pub fn escape_cell_counts(&self) -> (usize, usize) {
        escape::cell_counts(self)
    }

    /// The prefix-chain sweep's verdict alone, for tests against an independent oracle.
    pub fn chain_verdict(&self) -> Option<Verdict> {
        let mut s = Search {
            strict: true,
            refuse_forks: true,
            ..Search::default()
        };
        let t = self.clone();
        s.roots.insert(t.clone(), ());
        s.run(|d| Box::pin(async move { d.sweep_verdict(&t).await }))
    }

    /// Diagnostic version with each temporal run expanded to a single link.
    /// It shares the grammar and set primitives but performs every scheduled step.
    #[doc(hidden)]
    pub fn chain_verdict_expanded(&self) -> Option<Verdict> {
        let mut s = Search {
            strict: true,
            refuse_forks: true,
            expand_chain_runs: true,
            ..Search::default()
        };
        let t = self.clone();
        s.roots.insert(t.clone(), ());
        s.run(|d| Box::pin(async move { d.sweep_verdict(&t).await }))
    }

    /// The verdict of self by a search of its own.
    fn verdict_alone(&self) -> Verdict {
        if let Some(v) = sweep::front_sweep(self) {
            return v;
        }
        let mut s = Search {
            strict: true,
            refuse_forks: true,
            trials: Some(0),
            ..Search::default()
        };
        // The front sweep left `self` to the search above.
        s.swept.insert(self.clone(), None);
        let b = s.solve(self);
        let decided = s.refused.is_none();
        if (decided && b) || (s.refused == Some(Refusal::Fork) && self.empty_past_forks()) {
            Verdict::Empty
        } else if decided
            && (s.ids.get(self).is_some_and(|t| s.witnessed.contains(t)) || s.rep(self).is_some())
        {
            Verdict::Inhabited
        } else if (Search {
            strict: true,
            open_forks: true,
            ..Search::default()
        })
        .rep(self)
        .is_some()
        {
            // Before a refusal, a value is sought by a search that does not stop at a fork: it
            // takes a forked part as inhabited and keeps a value only once it is checked.
            Verdict::Inhabited
        } else {
            // Complexity tradeoff: a type the search neither proved empty nor showed inhabited by
            // a built value is refused, never called empty or inhabited, so a verdict is never
            // wrong; it gives up the answer itself. Why: the search is incomplete (the tradeoffs
            // at the Fork, Residues, TupleSplit and MorphismSplit sites), and the value builder
            // shows only values it can check: a closure is built only when a value of its value
            // type is built or decided by its group, or when its key type is empty, so it is never
            // called: known so without a search, or proved so in this one (`Searching::no_key`).
            // A key type whose emptiness rests on a type still being decided when the closure is
            // sought is proved empty only when a phase of `solve` ends, so a search that only
            // builds values (the second one here) gives it no closure. Trigger: no refusal was
            // named, and neither search built a value. Tests:
            // `l01_23_groups_and_refusals::refusals::each_refusal_names_its_cause` (`morphism_between`),
            // `l01_23_subtyping::witnesses::a_meet_of_cycles_is_shown_by_its_length` and
            // `l01_23_groups_and_refusals::judgments::a_morphism_cycle_through_an_empty_part_is_empty`.
            // COMPLEXITY.md Kept row "emptiness and subtyping of tuple and morphism parts". A
            // complete solution needs a value builder for every kind of type (closures included,
            // L2) and a complete search, exponential in the types (the subset construction at
            // a fork, a split of the box in every component); used: the two searches already
            // run, each polynomial in the types written (module comment), and nothing more.
            Verdict::Refused(s.refused.or(s.gave_up).unwrap_or(Refusal::NoWitness))
        }
    }

    /// A value of `self` built by the two searches of `verdict_alone`, the first that builds one,
    /// as a value (`Search::value`); `None` when neither builds one, or when the one built
    /// holds a closure or a struct. Nothing is kept: each call searches again. For tests, so
    /// an `Inhabited` verdict can be checked with [`Type::contains`] on the value it rests on.
    // Complexity tradeoff: the cost of `verdict_alone`'s searches, with no front sweep (it gives
    // a verdict, never a value) and no cache, against keeping the value of every verdict for a
    // query only tests make.
    pub fn witness(&self) -> Option<Value> {
        let mut s = Search {
            strict: true,
            refuse_forks: true,
            trials: Some(0),
            ..Search::default()
        };
        s.swept.insert(self.clone(), None);
        s.solve(self);
        if s.refused.is_none()
            && let Some(r) = s.rep(self)
            && let Some(v) = s.value(r)
        {
            return Some(v);
        }
        let mut s = Search {
            strict: true,
            open_forks: true,
            ..Search::default()
        };
        let r = s.rep(self)?;
        s.value(r)
    }

    /// Whether a search that does not end at a fork proves `self` empty with no fork under it:
    /// the search of [`group_verdicts`] with `self` its one root. Each fork is noted against
    /// the type being decided, and a part proved empty by one component is not charged with a
    /// fork met in another (`Searching::any_empty`), so a tuple with an empty component is
    /// empty whichever component comes first.
    // Complexity tradeoff: run only after the search of `is_empty` or `verdict_alone` ended at a
    // fork, wherever the fork was met (a test of where it was met, kept until
    // FAIL-judgments-query-order-seed, saved this search for a fork met in the last component
    // tried, but a part the fork is not under can still be empty, so answers depended on the
    // queries kept before), so a type decided without a fork costs what it did; one more search
    // over the same types, the cost of one group decision (module comment), once per type until
    // `forget_emptiness` (`PAST_FORKS`). Naive version: the first search alone, which
    // ends at the first fork in operand order, so `(F, E)` is refused and `(E, F)` is empty.
    // What is given up: an Empty that only a search following both sides of the fork proves
    // stays refused. Test: `l01_23_groups_and_refusals::refusals::a_tuple_with_an_empty_component_is_empty_in_either_order`.
    fn empty_past_forks(&self) -> bool {
        if let Some(e) = PAST_FORKS.with(|m| m.borrow().get(self).copied()) {
            return e;
        }
        let mut d = Search {
            strict: true,
            refuse_forks: true,
            blame: Some(Blames::default()),
            trials: Some(0),
            ..Search::default()
        };
        let b = d.solve(self);
        let causes = d.causes();
        let cause = d.refused.or(d.ids.get(self).and_then(|&i| causes[i]));
        let e = b && cause != Some(Refusal::Fork);
        PAST_FORKS.with(|m| m.borrow_mut().insert(self.clone(), e));
        e
    }

    /// Whether every value of `self` is in `other`: `self <: other`.
    pub fn subtype(&self, other: &Type) -> bool {
        Simulation::default().holds(self, other) || (self - other).is_empty()
    }

    /// The outcome of `self <: other`: `Empty` when it holds, `Inhabited` when a value of `self`
    /// outside `other` was built.
    ///
    /// Two routes give it: first the simulation, a proof of `<:` on lists of rows, then the
    /// verdict of `self - other`. Both are sound, so they never disagree where the search
    /// decides; this verdict is `(self - other).verdict()` except that it may be `Empty` where
    /// that one is refused: 3 of 3,999 random recursive pairs (tests `the_two_routes_agree_on_*`
    /// and `the_recorded_cases_are_decided_by_the_simulation` in `l01_23_subtyping::oracle`;
    /// COMPLEXITY.md K37).
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
/// is compared with the rows of `b` that share its first column, so unions keyed by a scalar
/// cost one row each, or with the rows whose atom names in one column may hold its own, where
/// those are fewer or none share it ([`ByName`]).
// Complexity tradeoff (COMPLEXITY.md K37): the naive version recomputes the relation until no
// pair changes, each round rereading every pair, O(pairs × rounds); the version before T6 made
// 4n² pairs, 0.5 s at n = 128, for the union of `nth_from_end(1..=n)` against itself plus one.
// Used: each pair
// counts its open choices and a failure is spread once along its readers, as in Horn
// satisfiability, O(needs) with O(log n) per lookup in `pairs`; a row equal to a row of `b`
// holds with no search. Given up: the proof is sufficient only, so a pair it cannot show goes
// to `Search`.
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
        let Some(needs) = self.rows(&a.p(), &b.p()) else {
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
        // Each set of literals of `a` within that of `b` by [`Lits::within`], which tests a
        // finite set against a cofinite one by walking the smaller of the finite set and the
        // values the cofinite one leaves out (COMPLEXITY.md F113).
        let same = a.bools & !b.bools == 0
            && a.ints.within(&b.ints)
            && a.rats.within(&b.rats)
            && a.floats.within(&b.floats)
            && a.f32s.within(&b.f32s)
            && a.strings.within(&b.strings)
            && (!a.structs || b.structs)
            && (a.morphisms.is_leaf() == Some(false) || a.morphisms == b.morphisms)
            && (!a.atoms.cofinite() || a.atoms == b.atoms)
            && (!a.tuples.rest || a.tuples == b.tuples);
        if !same {
            return None;
        }
        let mut needs = Vec::new();
        if !a.atoms.cofinite() {
            for (name, x) in a.atoms.names() {
                match b.atoms.names().get(name) {
                    None if b.atoms.cofinite() => {}
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
            let mut by_name = None;
            let mut split = Vec::new();
            for x in &xs {
                // A row whose first column no row of `b` shares, and holds tuples only, is
                // split there into one row per tuple shape of the column ([`tuple_rows`]): a
                // product distributes over a union in one component, so the rows hold the
                // values `x` holds, and each must lie under a row of `b`. A row under one row
                // of `b` has each of its rows under it, so the proof finds no less.
                //
                // Complexity tradeoff (COMPLEXITY.md K120): unsplit, `((0,) | … | (n-1,),)`
                // against `((0,),) | … | ((n-1,),)` met every row of `b`, and each pair
                // `((0,) | … | (n-1,), (i,))` met each shape of the column: n² pairs, and the
                // proof failed, leaving the difference to decide (1.7 s at n = 320). Split,
                // each row shares its first column with one row of `b`: O(n log n). Only
                // against two rows of `b` or more: against one there is no choice, each row of
                // the column meets that one row, and the check would cost each nested level
                // (`l01_26_type_resolution::bench::deep_ops`). Given up: only the first column
                // is split, and only when it holds tuples alone.
                if *len > 0
                    && ys.len() > 1
                    && !first.contains_key(&x[0])
                    && let Some(shapes) = tuple_rows(&x[0])
                {
                    split.extend(shapes.into_iter().map(|s| {
                        let head = Type::tuple(s.to_vec());
                        Row::new(
                            std::iter::once(head)
                                .chain(x[1..].iter().cloned())
                                .collect(),
                        )
                    }));
                    continue;
                }
                split.push(x.clone());
            }
            for x in &split {
                // A row of `b` equal to `x` holds it, whatever the other rows need.
                if whole.contains(x) {
                    continue;
                }
                // The rows sharing the first column, a choice that may leave out a row that holds
                // `x`, or the rows that may hold `x` by the atom names or literals of one column
                // ([`ByName`]), whichever are fewer; every row when neither applies.
                let near = (*len > 0).then(|| first.get(&x[0])).flatten();
                // One row of `b` leaves nothing to choose: it is taken without filing it.
                let tried = match near {
                    Some(r) if r.len() < 2 => r.clone(),
                    _ if ys.len() < 2 => ys.iter().collect(),
                    _ => {
                        let named = by_name.get_or_insert_with(|| ByName::new(&ys, *len));
                        match (near, named.rows(x)) {
                            (Some(r), Some(n)) if r.len() <= n.len() => r.clone(),
                            (_, Some(n)) => n,
                            (Some(r), None) => r.clone(),
                            (None, None) => ys.iter().collect(),
                        }
                    }
                };
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

/// The rows of the tuple shapes `t` is the union of, when it holds two or more and nothing
/// else: no scalar, atom, struct or function, and no tuple of every length. Exact: each tuple
/// part is the union of the rows [`Part::union_rows`] gives, or none is given.
fn tuple_rows(t: &Type) -> Option<Vec<Row>> {
    let p = t.p();
    let none = Lits::default();
    let scalars = p.bools != 0
        || [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings]
            .iter()
            .any(|l| **l != none);
    if scalars
        || p.structs
        || p.morphisms.is_leaf() != Some(false)
        || p.atoms.cofinite()
        || !p.atoms.names().is_empty()
        || p.tuples.rest
    {
        return None;
    }
    let mut out = Vec::new();
    for f in p.tuples.lens.values() {
        out.extend(f.union_rows()?);
    }
    (out.len() > 1).then_some(out)
}

/// The rows of the right side of a [`Simulation`] pair filed by the atom names of each column,
/// so that a row of the left side is compared only with rows that may hold it.
///
/// Why the rows left out cannot hold the row: [`Simulation::rows`] fails a pair whose left side
/// lists an atom name that the right side neither lists nor holds as one of every name it does
/// not list. So a row whose column `j` lists the name `n` lies only under rows whose column `j`
/// lists `n` or holds every unlisted name, and leaving the others out strikes no choice that
/// could hold. The rows sharing the first column, which [`Simulation::rows`] took alone before,
/// are a choice that may leave out a row that holds; where the rows found here are fewer they
/// are taken instead, a superset of the rows that hold, so the proof finds no less.
///
/// Complexity tradeoff: before (FAIL-types-loose-pairing-decided), a row whose first column
/// equals that of no row was compared with every row, and one whose first column many rows
/// share with each of them: `n` rows `(#m_i, #a_i)` against `n` rows `(#m_i | #k_i, #a_i)` made
/// `n^2` pairs (the forms of `(f_i, #a_i) | (h_i, #b_i)` against `(h_i, #a_i) | (f_i, #b_i) |
/// (h_i, #b_i)`, whose function `h_i` holds the marks of `f_i` and `h_i`), and so did `n` rows
/// `(#m, #a_i)` against `n` rows `(#m, #a_i | #b_i)`, as when every skipped function is one mark
/// (`Merged` in `zedc-types`). Naive version: every row tried, O(|xs|·|ys|) pairs; used: each
/// column of each row filed by each name it lists, O(Σ names) to file, made once per tuple
/// length and only when some row is not settled by one row sharing its first column; then, for
/// each row, the column of its with the fewest rows under its first name, O(len) lookups. What
/// is given up: columns that each list many names, shared or not, cost those names to file; a
/// row with no column listing a name is still compared with every row (or those sharing its
/// first column); and rows that each share a name with many rows in every column still meet
/// them all.
///
/// Literals are filed the same way (PERF-disjoint-rows-shared-shapes): [`Simulation::rows`]
/// fails a pair whose left side holds a literal of a kind (`int`, `rat`, `f64`, `f32`,
/// `string`) that the right side's set of that kind leaves out, so a row whose column `j` lists
/// the literal `v` lies only under rows whose column `j` lists `v` among a finite set of its
/// kind or holds a cofinite set of it. Complexity tradeoff: `m` rows `((#_, i) \ (#a, i), 0)`
/// against `m` rows `((#_, int), i | i + 1)` list no atom name in any column and share no first
/// column, so each row was compared with every row: `m^2` choices, 357 ms of 595 ms at
/// `m = 256` (load 44). Filed by literal, the column `0` meets one row: O(Σ literals) to file,
/// the size of the right side's literal sets, and O(len) lookups per row. Given up as for names:
/// a column listing many literals costs them to file each time the rows are filed.
struct ByName<'a> {
    named: HashMap<(usize, &'a str), Vec<&'a Row>>,
    /// Per column, the rows whose component there holds the atoms of every name it does not
    /// list.
    open: Vec<Vec<&'a Row>>,
    /// The rows by column, kind of literal ([`literal_sets`]) and a literal their component
    /// there lists in a finite set of that kind.
    valued: HashMap<(usize, usize, Value), Vec<&'a Row>>,
    /// Per column and kind of literal, the rows whose component there holds a cofinite set of
    /// that kind.
    open_valued: Vec<[Vec<&'a Row>; 5]>,
}

/// The literal sets of a component by kind, in the order [`ByName`] numbers the kinds.
fn literal_sets(p: &Parts) -> [&Lits; 5] {
    [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings]
}

impl<'a> ByName<'a> {
    fn new(ys: &'a [Row], len: usize) -> Self {
        let mut named = HashMap::<(usize, &str), Vec<&Row>>::new();
        let mut open = vec![Vec::new(); len];
        let mut valued = HashMap::<(usize, usize, Value), Vec<&Row>>::new();
        let mut open_valued: Vec<[Vec<&Row>; 5]> = (0..len).map(|_| Default::default()).collect();
        for y in ys {
            for (j, open) in open.iter_mut().enumerate() {
                match y[j].atom_names() {
                    Some(names) => {
                        for (n, _) in names {
                            named.entry((j, n)).or_default().push(y);
                        }
                    }
                    None => open.push(y),
                }
                let p = y[j].p();
                for (k, lits) in literal_sets(&p).into_iter().enumerate() {
                    if lits.cofinite {
                        open_valued[j][k].push(y);
                    } else {
                        for v in lits.values.iter() {
                            valued.entry((j, k, v.clone())).or_default().push(y);
                        }
                    }
                }
            }
        }
        ByName {
            named,
            open,
            valued,
            open_valued,
        }
    }

    /// The rows that may hold `x` by the column of `x` and its first atom name, or its first
    /// literal of a kind, that the fewest rows may hold; or none when no column of `x` lists a
    /// name or a literal in a finite set.
    fn rows(&self, x: &Row) -> Option<Vec<&'a Row>> {
        let mut lists: Vec<(&[&'a Row], &[&'a Row])> = Vec::new();
        for j in 0..self.open.len() {
            if let Some((n, _)) = x[j].atom_names().and_then(|mut names| names.next()) {
                let named = self.named.get(&(j, n)).map_or(&[][..], Vec::as_slice);
                lists.push((named, &self.open[j]));
            }
            let p = x[j].p();
            for (k, lits) in literal_sets(&p).into_iter().enumerate() {
                let Some(v) = lits.values.iter().next().filter(|_| !lits.cofinite) else {
                    continue;
                };
                let listed = self
                    .valued
                    .get(&(j, k, v.clone()))
                    .map_or(&[][..], Vec::as_slice);
                lists.push((listed, &self.open_valued[j][k]));
            }
        }
        let (listed, open) = lists
            .into_iter()
            .min_by_key(|(listed, open)| listed.len() + open.len())?;
        Some(listed.iter().chain(open).copied().collect())
    }
}

/// A type whose value is being built ([`Searching::rep`]).
struct Building {
    /// How many builds of it are under way, one inside the other.
    depth: u32,
    /// The number of closures taken to have a value when its outermost build began
    /// ([`Search::assumed`]).
    since: u64,
    /// Whether it was built again inside its outermost build.
    again: bool,
}

/// One query's state: the types being decided, assumed empty, each with its depth among them;
/// those decided; the types decided on assumptions still being made, in the order they were
/// decided, each with the depths of those assumptions; and the depths of the assumptions the
/// current decision has used.
#[derive(Default)]
struct Search {
    /// Each type read, by its number here; a type built apart from an equal one is compared
    /// with it in full once per read.
    ids: Ids,
    types: Vec<Type>,
    /// One answer per type: true, empty, until the rule fails for it.
    answer: Vec<bool>,
    /// The type being decided, which reads the answers of others.
    current: Option<usize>,
    readers: Vec<BTreeSet<usize>>,
    /// Types to decide again, since an answer they read changed.
    again: BTreeSet<usize>,
    /// The types of the round of [`Searching::drain`] under way not yet decided again, taken from
    /// `again` when the round starts. Their answers are not decisions: at the start of a phase
    /// each is `true` again, until it is decided. A drain started inside a decision takes them
    /// first, so a type is read as settled only once it is decided.
    round: BTreeSet<usize>,
    /// Types shown inhabited by a checked value; permanent.
    witnessed: BTreeSet<usize>,
    reps: ByType<Option<usize>>,
    /// The types whose failure in `reps` was kept while `past_fork` was set: a search not past
    /// a fork builds them again ([`Searching::rep`]).
    past_failures: ByType<()>,
    /// The values shown, each once, by number.
    shown: Vec<Rep>,
    /// The number here of each value of another search read ([`Rep::Of`]), by its list in
    /// `STORES` and its number there, so a value shared within that one is shared here too.
    foreign: DigestMap<(usize, usize), usize>,
    /// For each such value whose parts were read in ([`Search::local`]), the number of the value
    /// made of them.
    expanded: DigestMap<usize, usize>,
    /// Whether a value is in a type, by the class of the value ([`Search::class`]) and the type.
    members: HashMap<(usize, Type), Option<bool>, Digests>,
    /// The height of each value shown whose height is known ([`Search::value_height`]).
    heights: DigestMap<usize, Option<u64>>,
    /// Per tuple part a tuple of plain values was tested against ([`makeable`]), its
    /// rows filed by the values they may hold ([`RowIndex`]), made at the first such test and
    /// kept with the part, so that its id names no other part. A list and an expression may
    /// share an id, so each is keyed with whether it is an expression; and a leaf's id is its
    /// value whatever its length, so each is keyed with its length too, which a part with rows
    /// fixes (FAIL-kernel-candidates-key-past-columns: the index of the empty part of one
    /// length was read for a tuple of another, past its columns).
    row_indexes: HashMap<(bool, u64, usize), (Part<Row>, RowIndex)>,
    /// Per tuple part a tuple with a component that is not plain was tested against, its rows
    /// filed by the keys their columns may hold ([`Columns`]), keyed and kept as `row_indexes`
    /// is.
    columns: HashMap<(bool, u64, usize), (Part<Row>, Columns)>,
    /// The keys of the column types of `row_indexes` and `columns`, each type filed once per
    /// way of reading it.
    filer: Filer,
    /// Per value shown that was read as a plain value ([`Search::plain`]), that value, or `None`
    /// when it is not one.
    plain: DigestMap<usize, Option<Value>>,
    /// Per value shown whose key was read ([`Search::key`]), that key, or `None` when it has none.
    value_keys: DigestMap<usize, Option<Value>>,
    /// The class of each value shown that was given one, by its number.
    classes: DigestMap<usize, usize>,
    /// The classes of the values this search built whose keys no value of `STORES` has, by key,
    /// and the number of classes it gave.
    own_keys: HashMap<ValueKey, usize>,
    own_classes: usize,
    /// Each type read as the value type of a morphism.
    value_reads: BTreeSet<usize>,
    /// Types proved empty for good: a morphism with such a value type has no value. All other
    /// value types read as inhabited, since a closure can return itself.
    dead: BTreeSet<usize>,
    /// The types being decided, on the stack: met for the first time, or decided again by
    /// [`Searching::drain`].
    deciding: BTreeSet<usize>,
    /// For each type, the types it read (with the high bit set when the read did not establish
    /// emptiness), each with the search epoch when it was read.
    reads: Vec<Vec<(usize, usize)>>,
    /// For each type, each type in its `reads` with the epoch of its first entry there
    /// ([`Search::drop_reads_since`]).
    first_reads: Vec<DigestMap<usize, usize>>,
    /// The types whose value is being built, and how many closures rest on one of them.
    building: ByType<Building>,
    resting: usize,
    /// How many closures were taken to have a value while their value type was sought
    /// ([`Searching::find_rep`]), and the numbers of those still being tested, innermost last.
    assumed: u64,
    assuming: Vec<u64>,
    /// For each type whose kept failure read the missing value of another type, the value of
    /// `assumed` when the failure was kept, and whether it was already sought again inside a
    /// closure taken to have a value since ([`Searching::rep`]).
    provisional: ByType<(u64, bool)>,
    /// The representatives kept, in order, so those resting on a failed build are dropped.
    built: Vec<Type>,
    /// The types whose missing value the build under way has read.
    read: Vec<Type>,
    /// For each type, the kept failures that read its missing value: they are sought again when
    /// it gets one ([`Searching::retry`]).
    waiting: ByType<Vec<Type>>,
    /// Whether a type was settled in this phase, after answers that read it as inhabited.
    settled: bool,
    /// Whether kept results are left unread and each place a part counts as inhabited with
    /// nothing shown is noted, for a caller that takes `Refused`.
    strict: bool,
    /// Whether a fork of recursive rows ends the search; set for the decision of a verdict and
    /// for [`Type::is_empty`], not for the search of a value after a refused decision.
    refuse_forks: bool,
    /// Whether a fork of recursive rows counts as inhabited with nothing shown, before the box
    /// is narrowed; set for the search of a value after a refused decision and for the searches
    /// of [`Searching::refine`], which so follow no fork ([`Searching::tuples_on`]).
    open_forks: bool,
    /// How many times the search of a value kept a component whole at a fork
    /// ([`Searching::narrow_tuples`]), so that [`Searching::find_rep`] knows a narrowing met one.
    kept_forks: usize,
    /// Whether the value being sought is a component of a candidate tried past a fork: its own
    /// parts that meet a fork are then tried with no candidate of their own
    /// ([`Searching::find_rep`]). Kept for each value sought ([`Searching::rep`]).
    past_fork: bool,
    /// Why the search stopped, when it met a fork; set only when `refuse_forks`.
    refused: Option<Refusal>,
    /// The first place the search let a part count as inhabited with nothing shown: the cause
    /// of a refusal when no value of the root is built. With `blame`, only such a place met
    /// while no type was being decided.
    gave_up: Option<Refusal>,
    /// How many times a part counted as inhabited with nothing shown.
    give_ups: usize,
    /// For a search with several roots ([`Search::solve_all`]): each fork or part counted as
    /// inhabited with nothing shown, with the type being decided when it was met, in the order
    /// met. A fork then refuses the types that read that type ([`Search::causes`]) and the
    /// search goes on; with no type being decided, it ends the search as with one root.
    blame: Option<Blames>,
    is_group: bool,
    /// Uses the exact all-Top row identity for an additional Empty proof only.
    tuple_universe: bool,
    tuple_universes: HashMap<u64, Part<Row>, Digests>,
    canonical_blame: bool,
    in_subtype_check: bool,
    canonical_roots: BTreeSet<usize>,
    canonical_ready: Vec<bool>,
    blamed_node: Vec<bool>,
    /// Monotone step counter stamping entries in `reads` and `blame` for fork rollback.
    epoch: usize,
    /// When `open_forks` is turned on inside a settled decision search, the table state to
    /// roll back to and the types below `mark` that gained a reader at or above it.
    open_forks_mark: Option<(usize, usize, usize, bool)>,
    open_fork_readers: Vec<usize>,
    /// Whether this is the first walk over the types, in which what a type read is on record.
    walking: bool,
    /// Whether values are sought only among the tuple types as written.
    seeding: bool,
    /// Key types with no value shown yet.
    keys: BTreeSet<Type>,
    /// What is known of each list type met, by the rule on pure cycles.
    cycles: ByType<Option<Cycle>>,
    /// What is known of each list type met, by the sweep over prefix chains.
    chains: ByType<Option<ChainPlan>>,
    /// What is known of each root list type by the front sweep ([`Searching::swept`]): its
    /// verdict, with the checked value when it is inhabited; `None` outside the sweep's class.
    swept: ByType<Option<Option<Value>>>,
    /// Diagnostic uncompressed temporal run, used only by chain_verdict_expanded.
    expand_chain_runs: bool,
    /// The types the query asks about ([`Searching::solve`], [`Type::chain_verdict`]): the only
    /// ones [`Searching::prefix_chains`] decides.
    roots: ByType<()>,
    /// The atom types among the roots that are not lists ([`fields`]): one is never a list in
    /// the general fallback (`in_list_fallback`), so the lists in its payload are decided as
    /// roots.
    wraps: ByType<()>,
    /// Written list items and their field descendants (`fields`, X43 / R11-C4):
    /// allowed their own sweeps inside the enclosing list fallback. Generated
    /// residual literal tails are still skipped.
    items: ByType<()>,
    /// Nesting depth inside the general tuple/parts fallback for a list type outside
    /// [`Searching::prefix_chains`]; while non-zero, internal narrowed residual tail types go
    /// straight to the general decider without re-running `prefix_chains`.
    in_list_fallback: usize,
    /// The meet, difference or union of each pair of nodes the search built
    /// ([`Searching::cut`]), built once, by the nodes' local numbers ([`Type::node_id`]), which
    /// are never reused; the operands are kept with it. Read only by `entry`, never iterated.
    cuts: HashMap<(u64, u64, Cut), (Type, Type, Type), Digests>,
    /// Outer carriers of an exposed node, independent of its emptiness answer.
    outer_kinds: HashMap<u64, u16, Digests>,
    /// Exact scalar cell results, once per pair of allocation-local node numbers.
    scalar_cells: HashMap<(u64, u64, bool), bool, Digests>,
    /// The isolated morphism carrier of each shared diagram node.
    morphism_types: HashMap<u64, Type, Digests>,
    /// With a list, every closure whose keys are permitted as written is taken to have a value
    /// at once, and its value type is put on the list, to be shown to have a value after the
    /// search ([`optimistic_values`]).
    optimistic: Option<Vec<Type>>,
    /// For [`Type::empty_past_forks`]: how many components of boxes are being tried for
    /// emptiness ([`Searching::any_empty`]). A fork met outside such a trial ends the search.
    trials: Option<usize>,
}

/// What [`Searching::cut`] builds of two types.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Cut {
    Meet,
    Minus,
    Join,
}

impl Cut {
    fn of(self, x: &Type, y: &Type) -> Type {
        match self {
            Cut::Meet => x & y,
            Cut::Minus => x - y,
            Cut::Join => x | y,
        }
    }
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

/// One node in the DAG of finite prefix chains ending at the carrier cycle.
struct ChainNode {
    has_stop: bool,
    head: Type,
    emit: Option<Type>,
    depth: usize,
    child: usize,
    run: usize,
    /// For `depth >= 2`, the node reached after `run` steps of `(has_stop, head, emit)`.
    jump: Option<usize>,
}

/// Active depth-`>= 2` chain tokens in [`Searching::find_prefix_chains`] that share
/// `(has_stop, head, emit)`.
struct ChainGroup {
    has_stop: bool,
    head: Type,
    emit: Option<Type>,
    active: usize,
    /// Whether this generation already occurs in its active vector.
    listed: bool,
    jumping_next: usize,
    jumping_stop_next: bool,
    jump_target: Option<usize>,
    multi_target: bool,
}

/// The prime powers of `n`.
fn prime_powers(mut n: u64) -> Vec<(u64, u64)> {
    let mut out = Vec::new();
    let mut r = 2;
    while r <= n / r {
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
/// lengths are those equal to `at` modulo `period` for each of `all`, for one of `any` when
/// `any` is not empty, and for none of `none`, and 0 when `bare`.
struct Meet {
    stop: std::sync::Arc<str>,
    link: std::sync::Arc<str>,
    item: Type,
    bare: bool,
    all: Vec<(u64, u64)>,
    any: Vec<(u64, u64)>,
    none: Vec<(u64, u64)>,
}

impl Meet {
    /// Whether the rest length `n` is in the classes: one more is a length of the list.
    fn fits(&self, n: &BigUint) -> bool {
        let at = |&(p, at): &(u64, u64)| n % p == BigUint::from(at);
        self.all.iter().all(at)
            && (self.any.is_empty() || self.any.iter().any(at))
            && !self.none.iter().any(at)
    }

    /// What the rule on pure cycles says of the lengths, with the classes a length is sought in
    /// when it answers `Some`; `None` when it does not decide them.
    fn lengths(&self) -> Option<(Lengths, Vec<(u64, u64)>)> {
        match (
            self.any.is_empty(),
            self.all.is_empty(),
            self.none.is_empty(),
        ) {
            (true, _, _) => Some((residues_meet(&self.all, &self.none), self.all.clone())),
            (false, true, _) => union_classes(&self.any, &self.none),
            (false, false, true) => Some(meet_union(&self.all, &self.any)),
            (false, false, false) => None,
        }
    }
}

/// The lengths in every class of `all` and in one of `any`, with the classes a length is
/// sought in when some are: `all` and the first class of `any` that meets them. Classes meet
/// exactly when they agree modulo each prime power two of their periods share (the Chinese
/// remainder theorem), so the residue of `all` modulo the highest power of each prime of its
/// periods is kept once, and a class of `any` is tested against it on its own primes.
///
/// Complexity tradeoff: the naive form tests each class of `any` with every class of `all`,
/// O(|any| × |all|). Used: one pass over `all` and one lookup for each prime of each class of
/// `any`, O(n log n) in the classes and their periods, with a trial division of each distinct
/// period, O(sqrt p) for a period of `p` definitions. Nothing is given up. Tests:
/// `l01_23_subtyping::witnesses::a_union_of_cycles_less_one_is_decided` (the pairs, whose
/// lists are met with the class taken out) and `a_union_of_cycles_less_one_scales`.
fn meet_union(all: &[(u64, u64)], any: &[(u64, u64)]) -> (Lengths, Vec<(u64, u64)>) {
    // The highest power of each prime among the periods of `all`, and the residue there.
    let mut best: HashMap<u64, (u64, u64)> = HashMap::new();
    for &(period, at) in all {
        for (r, q) in prime_powers(period) {
            let (q0, at0) = *best.entry(r).or_insert((q, at % q));
            let m = q.min(q0);
            if at % m != at0 % m {
                return (Lengths::None, Vec::new());
            }
            if q > q0 {
                best.insert(r, (q, at % q));
            }
        }
    }
    let mut factors: HashMap<u64, Vec<(u64, u64)>> = HashMap::new();
    for &(p, at) in any {
        let meets = factors
            .entry(p)
            .or_insert_with(|| prime_powers(p))
            .iter()
            .all(|&(r, q)| {
                best.get(&r).is_none_or(|&(q0, at0)| {
                    let m = q.min(q0);
                    at % m == at0 % m
                })
            });
        if meets {
            let mut classes = all.to_vec();
            classes.push((p, at));
            return (Lengths::Some, classes);
        }
    }
    (Lengths::None, Vec::new())
}

/// The divisors of `n`, from its prime powers, in increasing order.
fn divisors(n: u64) -> Vec<u64> {
    let mut out = vec![1];
    for (r, q) in prime_powers(n) {
        let below = out.len();
        let mut power = r;
        loop {
            for i in 0..below {
                out.push(out[i] * power);
            }
            if power == q {
                break;
            }
            power *= r;
        }
    }
    out.sort_unstable();
    out
}

/// The lengths equal to `at` modulo `period` for one class of `any` and for none of `none`,
/// with the class a length is sought in when some are left. They are none when each class of
/// `any` lies inside one class of `none`; when a class of `any` lies inside none of them,
/// `residue_classes` decides the first such class alone: when it keeps a length, so does the
/// union. `None` when that class has none left or is refused, since whether the negated
/// classes cover the class of `any` jointly is the covering problem for residues (NP-hard).
///
/// A class `(p, r)` lies inside `(q, s)` exactly when `q` divides `p` and `r` is `s` modulo
/// `q`, so `(p, r)` lies inside a class of `none` exactly when the residue `r` modulo `p` is
/// in `covered(p)`: the residues modulo `p` some class of `none` with a period dividing `p`
/// holds. `covered` is built over the divisors of `p` in increasing order: `covered(d)` holds
/// the residues of the classes of `none` of period `d`, and those of `covered(d / r)` for each
/// prime `r` of `d` read modulo `d`, since every proper divisor of `d` divides some `d / r`.
/// Each `covered(d)` is built once, kept by `d` and shared by every period it divides.
///
/// Complexity tradeoff: `n` is the periods of the cycles of `any` and `none` together, the
/// definitions they cost (`period(p, k)` is `p` definitions), plus the classes. The naive form
/// decides each class of `any` against all of `none` with `residues_meet`, O(|any| × |none|)
/// tests (the split into open tuple types, 62x bytes at 8n, did the same); and testing each
/// class of `any` against each class of `none` whose period divides `p` costs the divisors of
/// `p` per class, which is not O(log n) (720720 has 240). Used: each `covered(d)` costs `d`
/// for each prime of `d`, and the divisors `d` of `p` sum to O(p log log p), so a period `p`
/// costs O(p log p) time and O(p log log p) memory, a class of `any` one lookup and a class of
/// `none` one mark: O(n log n) time and memory in all, the trial division of each period
/// O(sqrt p) besides; on the family of the scaling test it took 8.2 times the work at 8.5
/// times `n`, where the naive form took 11.5. What is given up: a class of `any` that only
/// several classes of `none` cover together is not decided here (the naive form decides it
/// when one prime split does, at the cost above; the caller keeps its other rules). Tests:
/// `l01_23_subtyping::witnesses::a_union_of_cycles_less_one_is_decided` and
/// `a_union_of_cycles_less_one_scales`; COMPLEXITY.md K34.
fn union_classes(any: &[(u64, u64)], none: &[(u64, u64)]) -> Option<(Lengths, Vec<(u64, u64)>)> {
    let mut negated: HashMap<u64, Vec<u64>> = HashMap::new();
    for &(q, s) in none {
        negated.entry(q).or_default().push(s % q);
    }
    // The residues covered modulo each divisor built so far; empty when none is.
    let mut covered: HashMap<u64, Vec<bool>> = HashMap::new();
    for &(p, r) in any {
        if !covered.contains_key(&p) {
            let primes: Vec<u64> = prime_powers(p).into_iter().map(|(r, _)| r).collect();
            for d in divisors(p) {
                if covered.contains_key(&d) {
                    continue;
                }
                let mut held = vec![false; d as usize];
                let mut some = false;
                for &s in negated.get(&d).into_iter().flatten() {
                    held[s as usize] = true;
                    some = true;
                }
                for &prime in primes.iter().filter(|&&prime| d % prime == 0) {
                    let below = &covered[&(d / prime)];
                    if !below.is_empty() {
                        for (x, h) in held.iter_mut().enumerate() {
                            *h |= below[x % below.len()];
                        }
                        some = true;
                    }
                }
                covered.insert(d, if some { held } else { Vec::new() });
            }
        }
        let held = &covered[&p];
        if held.is_empty() || !held[r as usize] {
            return match residue_classes(&[(p, r)], none) {
                (Lengths::Some, classes) => Some((Lengths::Some, classes)),
                _ => None,
            };
        }
    }
    Some((Lengths::None, Vec::new()))
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
/// decided by shares, a class shares refuses split again on `r` (`split_on`): some length is
/// left when one class has one, and none when no class has. Classes no negated class tells
/// apart are one class. The primes are tried in order, each
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
        match split_on(r, &mut split, none) {
            Lengths::Some => return (Lengths::Some, split),
            Lengths::None => return (Lengths::None, Vec::new()),
            Lengths::Refused => {}
        }
    }
    (Lengths::Refused, Vec::new())
}

/// Splits the lengths of `split` on the prime `r` into the classes modulo `q0 * r`, `q0` the
/// power of `r` the classes of `split` fix, and decides each class by shares; a class shares
/// refuses is split again on `r`, one level down, until no negated class has a finer power of
/// `r` to tell its classes apart. `Some` leaves the class that has a length pushed on `split`;
/// otherwise `split` is as it was. Lists whose length is in none of 0 modulo 2, 1 and 3 modulo
/// 4, 7 modulo 12 and 0 modulo 3 need two levels: modulo 2 the odd class is refused by shares
/// (1/2 + 1/2 + 1/6 over it), and modulo 4 each odd class is one negated class
/// (FAIL-periodic-lists-13375960689).
///
/// Complexity tradeoff: the naive split goes straight to the largest power of `r` among the
/// periods and decides each of its classes, as many as that power over `q0`, which is
/// exponential in the digits of the periods. Here only the classes some negated class meets
/// alone are tried, and one other that stands for the rest at its level, so the classes tried
/// are the nodes of the `r`-adic tree of the negated classes' residues plus one free child per
/// node: O(|none| · e) nodes, `e` the largest exponent of `r`, each one call of `shares`, which
/// is O(|split| · |none|). The former split went down one level only, the same cost per level,
/// and refused what needs two.
fn split_on(r: u64, split: &mut Vec<(u64, u64)>, none: &[(u64, u64)]) -> Lengths {
    // The power of `r` the classes of `split` fix, and the residue there.
    let (q0, at0) = split
        .iter()
        .filter_map(|&(period, at)| {
            let q = prime_powers(period).into_iter().find(|&(p, _)| p == r)?.1;
            Some((q, at % q))
        })
        .max()
        .unwrap_or((1, 0));
    let Some(q) = q0.checked_mul(r) else {
        return Lengths::Refused;
    };
    // The classes modulo `q` some negated class meets alone, and one other when they are not
    // all of them. When no negated class meets one alone, no class differs from another by
    // shares, and each is as refused as the lengths of `split`.
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
    if tried.is_empty() {
        return Lengths::Refused;
    }
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
        let l = match shares(split, none) {
            Lengths::Refused => split_on(r, split, none),
            l => l,
        };
        if l == Lengths::Some {
            return Lengths::Some;
        }
        split.pop();
        if l == Lengths::Refused {
            all_none = false;
        }
    }
    if all_none {
        Lengths::None
    } else {
        Lengths::Refused
    }
}

/// A class of lengths on the primes where it is finer than the lengths of `all`: (index of the
/// prime, power, residue) in the order of the primes.
type Fine = Vec<(usize, u64, u64)>;

/// A class `(power, residue)` modulo a power of one prime, with its value.
type ResidueValue = ((u64, u64), BigInt);

/// A length in the lengths of `all` and in none of `none`, chosen by the method of conditional
/// expectations with a pessimistic estimator (Raghavan 1988): the residue modulo the largest
/// power of each prime of the periods is chosen in turn, the residues not yet chosen taken as
/// uniform among those `all` allows, each prime on its own. The estimator is
/// `g(n) = Σ_c [n ∈ c] − [n ∈ a ∩ b]` over the entries `c` of `none`, with `a` and `b` two
/// entries of `none` that meet `all` and each other, or with no pair when the shares sum below
/// one: Hunter's bound (Hunter 1976) keeping one edge, a forest of one edge. Each residue is the
/// one for which the expectation of `g` is least, counted exactly in integers.
///
/// Proof that a length is found whenever the rule (`shares`, on the classes
/// `residue_classes` gives) finds one: `g(n) ≥ [n is in some class of none]` for every `n`,
/// since `g(n) = 0` when no class holds `n`, `g(n) = Σ ≥ 1` when some class holds it and `a ∩ b`
/// does not, and `g(n) = Σ − 1 ≥ 1` when `a ∩ b` holds it, as then `a` and `b` both do. The
/// rule answers `Some` when the shares sum below one, and then `E[g] < 1` with no pair; or
/// when they sum to one and two entries `a` and `b` that meet `all` meet each other, and then
/// `E[g] = 1 − share(a ∩ b)`, below one because `a ∩ b` meets the lengths of `all`: on each
/// prime the classes are balls of the `r`-adic integers, and balls that meet two by two share
/// a point, so the classes of `all`, `a` and `b` share a residue on each prime and, by the
/// Chinese remainder theorem, a length. The expectation of `g` given the residues chosen so far
/// is the average over the next residue of the expectation given that one too, so its least is
/// at most the average, and the expectation never rises. Once every residue is chosen `g(n)` is
/// an integer below one, so at most 0, and no class of `none` holds `n`. The counts are exact
/// (`BigUint` and `BigInt`), so no rounding can rise past one: the former choice in `f64`, by
/// the expected number of classes alone, took the tied residue 0 for
/// `none = [(3, 1), (6, 1), (3, 0), (6, 2)]` on both 2 and 3, and the length 0 is in `(3, 0)`
/// (KERNEL-witness-length-miss).
///
/// When the rule refuses, a length may still be found, and the caller checks it. The length is
/// at most the lcm of the periods, a number of as many digits as the periods have together.
fn greedy_length(all: &[(u64, u64)], none: &[(u64, u64)]) -> BigUint {
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
    let index: BTreeMap<u64, usize> = primes.keys().enumerate().map(|(i, &r)| (r, i)).collect();
    let primes: Vec<(u64, u64, u64, u64)> = primes
        .into_iter()
        .map(|(r, (top, q0, a0))| (r, top, q0, a0))
        .collect();
    // A class of `none` on the primes where it is finer than `all`, as (index of the prime,
    // power, residue) in the order of `primes`; `None` when no length of `all` is in it. On the
    // other primes it holds every residue `all` allows, so it is the same for every choice there.
    let fine = |(period, at): (u64, u64)| -> Option<Fine> {
        let mut out = Vec::new();
        for (r, q) in prime_powers(period) {
            let i = index[&r];
            let (_, _, q0, a0) = primes[i];
            if q <= q0 {
                if at % q != a0 % q {
                    return None;
                }
            } else if at % q0 != a0 {
                return None;
            } else {
                out.push((i, q, at % q));
            }
        }
        Some(out)
    };
    // How many times the lengths of `all` outnumber those of the class `c`, on the primes from
    // the `from`th on: at most the lcm of two periods.
    let ratio = |c: &[(usize, u64, u64)], from: usize| -> u128 {
        c.iter()
            .filter(|&&(i, ..)| i >= from)
            .map(|&(i, q, _)| u128::from(q / primes[i].2))
            .product()
    };
    // The terms of `g`, each with its sign (`true` for `+`); a class no length of `all` is in
    // adds 0 and is left out. `kept` holds the whole class of each term.
    let (kept, mut terms): (Vec<_>, Vec<(bool, Fine)>) = none
        .iter()
        .filter_map(|&c| Some((c, (true, fine(c)?))))
        .unzip();
    // The choices on every prime, and the sum of the classes' shares of them, stopped once it is
    // past them: each share is at least 1 over its period, and `n` shares summing to at most one
    // have periods summing to at least `n²` (Cauchy and Schwarz), so at most the square root of
    // twice the definitions are added.
    let whole: BigUint = primes
        .iter()
        .map(|&(_, top, q0, _)| BigUint::from(top / q0))
        .product();
    let mut sum = BigUint::ZERO;
    for (_, c) in &terms {
        sum += &whole / ratio(c, 0);
        if sum > whole {
            break;
        }
    }
    if sum == whole {
        // Two classes that meet, and their meet, which `all` meets by the proof above. Any
        // meeting pair will do for the proof. Two classes that both meet `all` meet each other
        // exactly when their fine parts do: on a prime where one of them is no finer than `all`,
        // its residue is the one `all` fixes, and the other's residue agrees with that one too.
        // So `meeting_pair` runs on the whole classes, at the cost given there.
        //
        // Complexity tradeoff (PERF-residue-length-cost): this used to try every pair for the
        // one whose meet is largest, O(classes² × primes of a period). Its comment claimed that
        // the classes number at most the square root of the definitions. That is false: the
        // rotations of one cycle give about `n` classes from `n` definitions. The largest meet
        // only lowered the estimate more and was not needed for the proof.
        let meet = |a: &[(usize, u64, u64)], b: &[(usize, u64, u64)]| {
            let (mut i, mut j, mut out) = (0, 0, Vec::new());
            while i < a.len() || j < b.len() {
                match (a.get(i), b.get(j)) {
                    (Some(&x), Some(&y)) if x.0 == y.0 => {
                        let m = x.1.min(y.1);
                        if x.2 % m != y.2 % m {
                            return None;
                        }
                        out.push(if x.1 >= y.1 { x } else { y });
                        (i, j) = (i + 1, j + 1);
                    }
                    (Some(&x), Some(&y)) if x.0 < y.0 => {
                        out.push(x);
                        i += 1;
                    }
                    (Some(&x), None) => {
                        out.push(x);
                        i += 1;
                    }
                    (_, Some(&y)) => {
                        out.push(y);
                        j += 1;
                    }
                    (None, None) => unreachable!("the loop stops when both are done"),
                }
            }
            Some(out)
        };
        if let Some((i, j)) = meeting_pair(&kept) {
            let m = meet(&terms[i].1, &terms[j].1).expect("the whole classes meet");
            terms.push((false, m));
        }
    }
    // The terms finer than `all` on each prime; only they tell its residues apart.
    let mut on: Vec<Vec<usize>> = vec![Vec::new(); primes.len()];
    for (t, (_, c)) in terms.iter().enumerate() {
        for &(i, ..) in c {
            on[i].push(t);
        }
    }
    let mut alive = vec![true; terms.len()];
    let mut rest = whole;
    let mut chosen: Vec<u64> = Vec::with_capacity(primes.len());
    for (k, &(r, top, q0, a0)) in primes.iter().enumerate() {
        // Complexity tradeoff: the expectation of `g` given a residue, less what every residue
        // shares, is the sum over the terms finer than `all` on this prime that hold it of the
        // term's choices left, `rest` over its ratio on the primes after this one. The least is
        // found on the tree of their residue classes (`least_residue`), not by trying every
        // residue: O(terms on the prime × (digits of the power + primes of a period)) operations,
        // the divisions, additions and comparisons among them on numbers of at most the digits
        // of the lcm, so
        // O(classes × primes of a period) such divisions and O(classes × primes of a period²)
        // small operations in all, against
        // O(primes² × residues × classes) for the former choice in `f64`, which tried every
        // residue against every class on every prime and whose rounding could not be trusted
        // near one.
        rest /= top / q0;
        let mut nodes: BTreeMap<(u64, u64), BigInt> = BTreeMap::new();
        for &t in &on[k] {
            let (plus, c) = &terms[t];
            let &(_, q, res) = c.iter().find(|&&(i, ..)| i == k).expect("the term is on k");
            if alive[t] {
                let w = BigInt::from(&rest / ratio(c, k + 1));
                *nodes.entry((q, res)).or_default() += if *plus { w } else { -w };
            }
        }
        let (_, d) = least_residue(r, q0, a0, nodes.into_iter().collect());
        for &t in &on[k] {
            let &(_, q, res) = terms[t].1.iter().find(|&&(i, ..)| i == k).expect("on k");
            alive[t] &= d % q == res;
        }
        chosen.push(d);
    }
    // The length below the lcm with the chosen residues, by the Chinese remainder theorem.
    let (mut n, mut m) = (BigUint::ZERO, BigUint::from(1u32));
    for (&(_, q, _, _), &d) in primes.iter().zip(&chosen) {
        let below = |x: &BigUint| u64::try_from(x % q).expect("a residue is below q");
        let inv = inverse(below(&m), q).expect("m is a product of other primes' powers");
        let (x, y) = (d % q, below(&n));
        let gap = if x >= y { x - y } else { x + (q - y) };
        let step = u128::from(gap) * u128::from(inv) % u128::from(q);
        n += &m * u64::try_from(step).expect("a residue is below q");
        m *= q;
    }
    if n == BigUint::ZERO { m } else { n }
}

/// The residue `d`, equal to `res` modulo `q`, for which the sum of the values of the classes
/// `(power, residue)` of `nodes` that hold `d` is least, with that sum: the classes are those
/// modulo powers of the prime `p` above `q`, inside the class of `res`. Classes modulo powers of
/// one prime are nested or apart, so they form a tree: the residues modulo `q * p` that no class
/// lies in hold none of them, and each other one is searched on its own. Every class is passed
/// down once per power of `p` below its own, so the work is the classes times the digits of
/// the largest power, in operations on residues and in additions and comparisons of values
/// (numbers of up to the digits of the lcm); the residues no class holds are never listed.
fn least_residue(p: u64, q: u64, res: u64, nodes: Vec<ResidueValue>) -> (BigInt, u64) {
    if nodes.is_empty() {
        return (BigInt::ZERO, res);
    }
    let q1 = q * p;
    let mut groups: BTreeMap<u64, (BigInt, Vec<ResidueValue>)> = BTreeMap::new();
    for ((qn, rn), v) in nodes {
        let g = groups.entry(rn % q1).or_default();
        match qn == q1 {
            true => g.0 += v,
            false => g.1.push(((qn, rn), v)),
        }
    }
    let mut best = ((groups.len() as u64) < p).then(|| {
        let free = (0..p)
            .map(|j| res + j * q)
            .find(|s| !groups.contains_key(s))
            .expect("fewer groups than residues");
        (BigInt::ZERO, free)
    });
    for (s, (own, inner)) in groups {
        let (v, d) = least_residue(p, q1, s, inner);
        let v = v + own;
        if best.as_ref().is_none_or(|(b, _)| v < *b) {
            best = Some((v, d));
        }
    }
    best.expect("a residue is found")
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
    match meeting_pair(&meeting) {
        None => Lengths::None,
        Some(_) => Lengths::Some,
    }
}
fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// Two classes `(period, residue)` of `classes` that share a length, by their indices, or
/// `None` when they are pairwise disjoint. The classes `(p, r)` and `(q, s)` meet exactly when
/// `r = s` modulo `gcd(p, q)` (Chinese remainder theorem).
///
/// Complexity tradeoff (PERF-residue-length-cost): the naive search tries every pair, which is
/// O(k²) gcds for `k` classes. That is quadratic in the definitions, because the rotations of
/// one cycle of `p` definitions give `p - 1` classes modulo `p`. Measured through types, it took
/// 12.3 times the instructions per 8 times the definitions
/// (`a_list_less_the_rotations_of_one_cycle_scales`). This search groups the classes by period:
/// - In one group, two classes meet exactly when their residues are equal: one hash lookup per
///   class.
/// - For two groups of periods `p` and `q`, with `g = gcd(p, q)`, each group's residues modulo
///   `g` go into a hash map. Each map is built once per group and distinct `g` and kept, and the
///   smaller of the two maps is looked up in the larger.
///
/// The cost, for the callers' classes: every class meets the lengths of `all`, the shares sum
/// to at most one, and all classes of one period `p` have one share `1 / ρ_p` with
/// `ρ_p <= p`. Every distinct period is the period of its own cycle of `p` definitions, so with
/// `a_p` classes of period `p`, `Σ a_p / ρ_p <= 1` and `Σ ρ_p <= Σ p <= n`. Then:
/// - The number of groups is `D <= sqrt(2n)` (distinct periods summing to at most `n`), so
///   there are at most `n` pairs of groups.
/// - The lookups cost `Σ_{p<q} min(a_p, a_q) <= Σ sqrt(a_p a_q) <= (Σ sqrt(a_p))² / 2`. By
///   Cauchy and Schwarz that is at most `(Σ a_p / ρ_p)(Σ ρ_p) / 2 <= n / 2`.
/// - The maps cost `a_p` for each distinct `g` dividing `p`, so `Σ a_p d(p) <= n · max d(p)`,
///   where `d` counts divisors. `d(p) = p^O(1 / log log p)` is not bounded by a power of `log n`.
///   It is at most 240 for `p` below 10^6.
///
/// So the cost is O(n · max d(p)) hash operations in place of O(n²).
fn meeting_pair(classes: &[(u64, u64)]) -> Option<(usize, usize)> {
    let mut groups: Vec<(u64, HashMap<u64, usize>)> = Vec::new();
    let mut slot: HashMap<u64, usize> = HashMap::new();
    for (i, &(p, r)) in classes.iter().enumerate() {
        let s = *slot.entry(p).or_insert_with(|| {
            groups.push((p, HashMap::new()));
            groups.len() - 1
        });
        match groups[s].1.entry(r % p) {
            Entry::Occupied(e) => return Some((*e.get(), i)),
            Entry::Vacant(e) => {
                e.insert(i);
            }
        }
    }
    // Each group's residues modulo a divisor `g` of its period, with a class of each.
    let mut down: HashMap<(usize, u64), HashMap<u64, usize>> = HashMap::new();
    for a in 0..groups.len() {
        for b in 0..a {
            let g = gcd(groups[a].0, groups[b].0);
            for s in [a, b] {
                down.entry((s, g))
                    .or_insert_with(|| (groups[s].1.iter()).map(|(&r, &i)| (r % g, i)).collect());
            }
            let (x, y) = (&down[&(a, g)], &down[&(b, g)]);
            let (small, large) = if x.len() <= y.len() { (x, y) } else { (y, x) };
            if let Some((r, &i)) = small.iter().find(|(r, _)| large.contains_key(r)) {
                return Some((i, large[r]));
            }
        }
    }
    None
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
    // One remainder of the length per distinct period, not per class: a list `none` of many
    // classes of few periods (classes disjoint from `all` among them, which no share counts)
    // took one division of the lcm-sized length per class, Θ(n^1.5 √log n) word operations
    // when every class is charged its period (XR-wlen round 1, Gemini seat, measured on this
    // function alone; through types `a_list_of_cycles_less_many_disjoint_classes_scales` sees
    // no difference at 142_511 definitions); distinct periods sum to at most `n`, so at most
    // `sqrt(2n)` divisions are taken, each looked up by period.
    let fits = |n: &BigUint| {
        let mut rem: HashMap<u64, u64> = HashMap::new();
        let mut at = |p: u64| {
            *rem.entry(p)
                .or_insert_with(|| u64::try_from(n % p).expect("a remainder below a u64 period"))
        };
        all.iter().all(|&(p, r)| at(p) == r) && none.iter().all(|&(p, r)| at(p) != r)
    };
    let (lengths, classes) = residue_classes(all, none);
    let classes = match lengths {
        // The rule has shown no length is in every class of `all` and none of `none`.
        Lengths::None => return None,
        Lengths::Some => classes,
        Lengths::Refused => all.to_vec(),
    };
    // Complexity tradeoff: the length is one choice by conditional expectations, not the least
    // length. Whenever the rule finds a length (`lengths == Lengths::Some`) the choice gives
    // one, by the proof at `greedy_length`; only when the rule refuses can it miss, and then no
    // length is given and a tuple or atom holding such a list gets `Refused(NoWitness)`. The
    // least length, found by sieving the steps from 1 (the former `least_length`), costs the
    // steps passed, up to the lcm of the periods, exponential in the number of cycles: the
    // meet of `period(p, p - 1)` over the first nine primes took 31 s. A search of the residues
    // modulo each prime power with backtracking (the fix KERNEL-witness-length-miss proposed)
    // would also find the lengths the rule refuses, but is exponential in the primes in the
    // worst case: finding a length in no class of a list is NP-hard even when a period costs
    // its value in definitions, since 3-SAT reduces to it (a prime per variable with its
    // residues 2 and above taken out, so the residue 0 or 1 is the variable's value, and per
    // clause the one class modulo the product of its three primes where its literals are all
    // false; a length is left exactly when the formula is satisfiable). The estimator needs no
    // backtracking and finds a length wherever the rule finds one. Tests:
    // `l01_23_subtyping::witnesses::a_meet_of_cycles_is_shown_by_its_length`,
    // `the_meet_of_prime_cycles_scales`, `periodic_lists_agree_with_their_lengths` and its run
    // at a fixed seed, `empty::tests::the_residue_length_agrees_with_a_scan` and
    // `the_three_sat_reduction_at_residue_length_is_correct` (the reduction checked on 3-SAT
    // formulas against brute force, both ways);
    // COMPLEXITY.md K34. Used: O(classes × primes of a period) divisions of numbers of at most
    // the digits of the lcm and O(classes × primes of a period²) small operations, plus
    // O(n · max d(p)) hash operations for the meeting pair when the shares sum to exactly one
    // (`meeting_pair`, with the proof; it was O(classes²));
    // the check `fits` takes one remainder of the length per class, the same order. When the
    // rule finds a length and every class is charged its period in definitions `n`, this is
    // O(n log n) operations on words of log n bits: classes whose shares sum to at most one
    // have periods summing to at least the classes squared (Cauchy–Schwarz), so they number at
    // most `sqrt(n)`, each with at most `log n` primes; the lcm has at most `sqrt(2n) log n`
    // bits, its distinct periods summing to at most `n`, so each division, addition or
    // comparison of such numbers is O(sqrt(n)) words. That charge fails when classes are
    // rotations of one cycle, which share its definitions: about n/4 rotations of one cycle of
    // period n/2 beside cycles of about sqrt(n) distinct periods near sqrt(n) give about n^1.5
    // word operations here, and the rule itself (`residue_classes`, `shares`) factors and sums
    // every class again on each branch of a split. Measured through types
    // (PERF-residue-length-cost, `witnesses/bench.rs`), with rotations of cycles at 8 times the
    // definitions: a meeting pair among about `n` rotations was 12.3 times the instructions
    // with the old all-pairs search and is 8.42 times with `meeting_pair` (load 32). A split
    // by `residue_classes` on two prime cycles is 8.05 times (load 25), and the refused rule
    // on two cycles is 8.20 times (load 29). The word-operation bound for the rotations is not
    // proved, so these ratios are measurements only. The length is a `BigUint`, never walked.
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
// Complexity tradeoff (COMPLEXITY.md K24): the naive region keeps what is known per tuple type
// and component and tests each tuple type apart, O(N) in the `N` components written but with a
// test per component even where many tuple types share its type. Used: one cell per component
// and distinct type, tested once for every tuple type sharing it, and retested only when its
// component changed; still O(N), the input's own size and a lower bound (DESIGN.md L1.23), with
// about 3.4 times fewer instructions at c = 128 to 512 columns. Tradeoffs: the cell table and the
// change log cost memory O(N); a prefix trie weighed against it measured `c^2.93`.
#[derive(Default)]
struct Region {
    /// First column to test, chosen from the shared outer-carrier constraints.
    priority: usize,
    /// A contradiction in the original box and part, proved from outer carriers.
    structural_empty: bool,
    r: Vec<Type>,
    atoms: Vec<Row>,
    index: DigestMap<Row, usize>,
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
    forked_holds: Vec<(usize, usize, ForkSave)>,
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
    /// The value numbered `at` in the list `store` of `STORES`, built by the search of another
    /// group's verdicts; `of`, when it is the value of that member, so it is in that type with
    /// no test. It is read in ([`Search::local`]) one level at a time, when a test needs its parts.
    Of {
        store: usize,
        at: usize,
        of: Option<Type>,
    },
    /// A closure of the morphism type it was shown for; it may be recursive. It is in that
    /// morphism type; which of its morphisms it is, is not kept, so whether it is in a morphism
    /// part is known only when the part holds all morphisms or none, or names no morphism type
    /// but that one ([`Searching::closure_member`]).
    Closure(Morphism),
    Struct,
}

impl Rep {
    /// The numbers of the values it is made of, in the list that holds it.
    fn parts(&self) -> Vec<usize> {
        match self {
            Rep::Tuple(vs) => vs.clone(),
            Rep::Atom(_, p) => vec![*p],
            Rep::List { item, .. } => vec![*item],
            _ => vec![],
        }
    }

    /// The key of a value that is neither a closure nor a value of another search, with each
    /// part given as its class.
    fn key(&self, class: impl Fn(usize) -> usize) -> ValueKey {
        match self {
            Rep::Value(x) => ValueKey::Value(x.clone()),
            Rep::Tuple(vs) => ValueKey::Tuple(vs.iter().map(|&v| class(v)).collect()),
            Rep::Atom(name, p) => ValueKey::Atom(name.clone(), class(*p)),
            Rep::List {
                stop,
                link,
                item,
                len,
            } => ValueKey::List {
                stop: stop.clone(),
                link: link.clone(),
                item: class(*item),
                len: len.clone(),
            },
            Rep::Struct => ValueKey::Struct,
            // Its two callers, `stored_class` and `Search::class`, answer `Of` and `Closure` in
            // the arms above the one that calls `key`.
            Rep::Of { .. } | Rep::Closure(_) => unreachable!("a value with no key"),
        }
    }
}

/// A value, with each of its parts given as its class: two values with one key are equal. A
/// value's class is a number given to it and to every value equal to it, so that the membership
/// of a value in a type, a function of the value, is tested once for all values equal to it
/// ([`Searching::member_known`]). A closure is not compared: each has a class of its own.
#[derive(Clone, PartialEq, Eq, Hash)]
enum ValueKey {
    Value(Value),
    Tuple(Vec<usize>),
    Atom(Arc<str>, usize),
    List {
        stop: Arc<str>,
        link: Arc<str>,
        item: usize,
        len: BigUint,
    },
    Struct,
}

/// The classes of the values of `STORES`, numbered up from 0; a search numbers the classes of
/// the values it builds itself down from `usize::MAX` ([`Search::class`]). The keys hold atom
/// names, a program's text, so they keep the standard map's seeded hasher ([`DigestMap`]).
#[derive(Default)]
struct Classes {
    keys: HashMap<ValueKey, usize>,
    /// The class of each value kept, by its list in `STORES` and its number there.
    stored: DigestMap<(usize, usize), usize>,
}

/// The class of the value numbered `at` in the list `store` of `STORES`. The value and each of
/// its parts not yet given a class are given one, the parts first, on a list of their own rather
/// than the thread's stack, so a value nested to any depth is read with no more of the stack
/// than a shallow one. Each value kept is given its class once for all searches: it is a
/// function of the value, and the lists are never changed until `Type::forget_emptiness`, which
/// drops the classes with them.
fn stored_class(store: usize, at: usize) -> usize {
    CLASSES.with(|c| {
        STORES.with(|st| {
            let (mut c, st) = (c.borrow_mut(), st.borrow());
            let mut todo = vec![(store, at)];
            while let Some(&(s, a)) = todo.last() {
                if c.stored.contains_key(&(s, a)) {
                    todo.pop();
                    continue;
                }
                let rep = &st[s][a];
                let parts: Vec<(usize, usize)> = match rep {
                    Rep::Of { store, at, .. } => vec![(*store, *at)],
                    r => r.parts().into_iter().map(|p| (s, p)).collect(),
                };
                let missing: Vec<_> = (parts.into_iter())
                    .filter(|p| !c.stored.contains_key(p))
                    .collect();
                if !missing.is_empty() {
                    todo.extend(missing);
                    continue;
                }
                todo.pop();
                let next = c.keys.len() + c.stored.len();
                let class = match rep {
                    Rep::Of { store, at, .. } => c.stored[&(*store, *at)],
                    Rep::Closure(_) => next,
                    r => {
                        let key = r.key(|p| c.stored[&(s, p)]);
                        *c.keys.entry(key).or_insert(next)
                    }
                };
                c.stored.insert((s, a), class);
            }
            c.stored[&(store, at)]
        })
    })
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
    /// Narrowing alone, for [`key_pieces`]: a piece it does not prove empty with no fork sets
    /// `failed` and stops the split.
    Narrow {
        failed: &'a mut bool,
    },
    Seek {
        len: usize,
        found: &'a mut Option<usize>,
    },
}

const NON_EMPTY_READ: usize = 1 << (usize::BITS - 1);

#[inline]
fn pack_read(node: usize, empty_dep: bool) -> usize {
    if empty_dep {
        node
    } else {
        node | NON_EMPTY_READ
    }
}

#[inline]
fn unpack_read(packed: usize) -> (usize, bool) {
    (packed & !NON_EMPTY_READ, (packed & NON_EMPTY_READ) == 0)
}

impl Search {
    /// Runs `root` and the calls it makes on a stack of their own, on this search's state.
    fn run<V: Unpin + 'static>(
        &mut self,
        root: impl for<'m> FnOnce(&'m Searching<'m>) -> Pin<Box<dyn Future<Output = V> + 'm>>,
    ) -> V {
        let _compound = super::CompoundScope::enter();
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
        self.solve_all(std::slice::from_ref(root))[0]
    }

    /// Decides each of `roots` by one search ([`Searching::solve`]), so a type read from
    /// several roots is decided once: whether each is empty, in order.
    fn solve_all(&mut self, roots: &[Type]) -> Vec<bool> {
        let roots = roots.to_vec();
        self.run(|d| Box::pin(async move { d.solve(&roots).await }))
    }

    /// A value in `t`, if one is found ([`Searching::rep`]).
    fn rep(&mut self, t: &Type) -> Option<usize> {
        let t = t.clone();
        self.run(|d| Box::pin(d.rep(&t)))
    }

    /// Re-evaluates blamed non-empty nodes reachable from `roots`, so clean disjunction arms
    /// supersede blamed ones without re-running the search.
    fn settle_canonical_blame(&mut self, roots: &[Type]) {
        let roots = roots.to_vec();
        self.run(|d| Box::pin(d.settle_canonical_blame(roots)));
    }

    /// Drops every kept failure, between phases of a search, when no value is being built.
    fn forget_failures(&mut self) {
        self.reps.retain(|_, r| r.is_some());
        self.waiting.clear();
        self.read.clear();
        self.provisional.clear();
    }

    /// The end of a phase of [`Searching::solve`], once each inhabited answer was tried for a
    /// value, `new` when one was found: whether the phases are over, or another starts.
    fn end_phase(&mut self, open: Vec<usize>, new: bool) -> bool {
        if !self.again.is_empty() {
            return false;
        }
        // Value types still empty with every morphism value read as inhabited are empty:
        // read them so, and start again.
        let rest = self.fork_resting();
        let fresh: Vec<usize> = (self.value_reads.iter().copied())
            .filter(|&v| self.answer[v] && !self.dead.contains(&v) && !rest[v])
            .collect();
        if !fresh.is_empty() || std::mem::take(&mut self.settled) {
            self.dead.extend(fresh);
            for t in 0..self.types.len() {
                if !self.witnessed.contains(&t) && !self.dead.contains(&t) {
                    self.answer[t] = true;
                    if let Some(b) = self.blamed_node.get_mut(t) {
                        *b = false;
                    }
                    self.again.insert(t);
                }
            }
            self.forget_failures();
            return false;
        }
        if !new {
            return true;
        }
        for t in open {
            if !self.witnessed.contains(&t) {
                self.answer[t] = true;
                if let Some(b) = self.blamed_node.get_mut(t) {
                    *b = false;
                }
                self.again.insert(t);
            }
        }
        self.again.is_empty()
    }

    /// Notes the first place a part counted as inhabited with nothing shown. A search with
    /// `blame` notes it against the type being decided, and as `gave_up` only when there is none,
    /// so a root is never given the cause met in the decision of a type it does not read.
    fn give_up(&mut self, r: Refusal) {
        self.give_ups += 1;
        // A speculative value search keeps its uncertainty counter, but no permanent
        // refusal cause: the surrounding proof did not rely on that search.
        if self.open_forks && self.blame.is_some() {
            return;
        }
        let ep = self.epoch;
        match (&mut self.blame, self.current) {
            (Some(blame), Some(c)) if !self.open_forks => {
                blame.push((c, r, ep));
                if !self.canonical_blame {
                    self.blamed_node[c] = true;
                }
            }
            (Some(_), _) if self.open_forks && self.is_group => {}
            _ if self.strict
                && self
                    .gave_up
                    .is_none_or(|old| Self::refusal_rank(r) < Self::refusal_rank(old)) =>
            {
                self.gave_up = Some(r);
            }
            _ => {}
        }
    }

    fn add_reader(&mut self, u: usize, c: usize) -> bool {
        if self.open_forks_mark.is_some_and(|(m, ..)| u < m && c >= m) {
            self.open_fork_readers.push(u);
        }
        self.readers[u].insert(c)
    }

    /// Notes that `c` read `packed` ([`pack_read`]) at epoch `ep`, the epoch now or later than
    /// that of every read of `c` before it.
    fn push_read(&mut self, c: usize, packed: usize, ep: usize) {
        self.reads[c].push((packed, ep));
        self.first_reads[c]
            .entry(unpack_read(packed).0)
            .or_insert(ep);
    }

    /// The reads of `c` taken out in full, with its first reads.
    fn take_reads(&mut self, c: usize) -> Vec<(usize, usize)> {
        self.first_reads[c].clear();
        std::mem::take(&mut self.reads[c])
    }

    /// Takes out the reads `c` made from epoch `ep` on, packed ([`pack_read`]), and drops `c`
    /// from the readers of each type it no longer reads.
    // Complexity tradeoff (COMPLEXITY.md K102): the naive test scans the reads kept for each
    // read dropped, O(D K); a set of the kept reads, built at each call, made it O(D + K)
    // expected, but K is all that `c` read before the snapshot, so `n` rollbacks of one type
    // that reads more at each cost O(n^2) in all: the pair type met with `n` forked
    // differences, which `Type::empty_past_forks` searches one difference at a time, took
    // 2.23e9 and 3.43e10 instructions at n 512 and 4096 (15.3 times; FAIL-refusals-forked-pair-
    // bench). Used: the epoch of the first read of each type, kept as reads are pushed
    // (`first_reads`). The epochs along `reads[c]` do not fall, so a type read before `ep`
    // has its first read before `ep`, and one whose first read is at `ep` or later has none
    // kept: O(D) expected for D reads dropped. Given up: one map entry per type read.
    fn drop_reads_since(&mut self, c: usize, ep: usize) -> Vec<usize> {
        let start = self.reads[c].partition_point(|&(_, e)| e < ep);
        let dropped: Vec<usize> = self.reads[c].drain(start..).map(|(p, _)| p).collect();
        for &packed in &dropped {
            let (u, _) = unpack_read(packed);
            let first = &mut self.first_reads[c];
            if first.get(&u).is_some_and(|&e| e >= ep) {
                first.remove(&u);
                self.readers[u].remove(&c);
            }
        }
        dropped
    }

    /// Takes out the blame of `c` added from epoch `ep` on, keeping the blame of other types in
    /// its order. The epochs of the blame rise, so its start is found by binary search.
    fn take_blame_since(&mut self, c: Option<usize>, ep: usize) -> Vec<(usize, Refusal)> {
        let Some(b) = &mut self.blame else {
            return Vec::new();
        };
        let start = b.partition_point(|&(_, _, e)| e < ep);
        let mut saved = Vec::new();
        let mut k = start;
        for idx in start..b.len() {
            if Some(b[idx].0) == c {
                saved.push((b[idx].0, b[idx].1));
            } else {
                b.copy_entry(k, idx);
                k += 1;
            }
        }
        b.truncate(k);
        saved
    }

    fn push_open_forks(&mut self) -> Option<(usize, usize, usize, bool)> {
        if self.deciding.is_empty() && self.open_forks_mark.is_none() {
            let mark = (
                self.types.len(),
                self.blame.as_ref().map_or(0, |b| b.len()),
                self.dead.len(),
                self.settled,
            );
            self.open_forks_mark = Some(mark);
            Some(mark)
        } else {
            None
        }
    }

    /// Drops types numbered from `mark` on, added while `open_forks` was turned on inside a
    /// decision search, so its table holds only answers decided under `refuse_forks`.
    // Complexity tradeoff (COMPLEXITY.md K102): the naive undo scans every reader set for the
    // types dropped, O(T log T); [`Self::add_reader`] logs each older type that gained a newer
    // reader, so the undo splits only those sets, and each split is O(log T) plus what it drops.
    fn pop_open_forks(
        &mut self,
        (mark, blame_len, dead_len, settled): (usize, usize, usize, bool),
    ) {
        self.open_forks_mark = None;
        let _ = self.again.split_off(&mark);
        let _ = self.round.split_off(&mark);
        let _ = self.witnessed.split_off(&mark);
        let _ = self.value_reads.split_off(&mark);
        let _ = self.dead.split_off(&mark);
        if self.dead.len() == dead_len {
            self.settled = settled;
        }
        let _ = self.deciding.split_off(&mark);
        if let Some(blame) = &mut self.blame {
            blame.truncate(blame_len);
        }
        for u in self.open_fork_readers.drain(..) {
            let _ = self.readers[u].split_off(&mark);
        }
        for ty in self.types.drain(mark..) {
            self.ids.remove(&ty);
        }
        self.answer.truncate(mark);
        if self.canonical_ready.len() > mark {
            self.canonical_ready.truncate(mark);
        }
        if self.blamed_node.len() > mark {
            self.blamed_node.truncate(mark);
        }
        self.readers.truncate(mark);
        self.reads.truncate(mark);
        self.first_reads.truncate(mark);
    }

    fn refusal_rank(r: Refusal) -> (u8, usize) {
        match r {
            Refusal::Fork => (0, 0),
            Refusal::Group => (1, 0),
            Refusal::Residues => (2, 0),
            Refusal::SharedCells(j) => (3, j),
            Refusal::TupleSplit => (4, 0),
            Refusal::MorphismSplit => (5, 0),
            Refusal::NoWitness => (6, 0),
        }
    }

    /// For a search with `blame`, the cause each type's answer may rest on: a fork met in the
    /// decision of a type it read, directly or through others, else the highest-priority part
    /// counted as inhabited with nothing shown in such a decision. A non-fork cause does not
    /// propagate through a type proved empty or shown inhabited by a checked value.
    fn causes(&self) -> Vec<Option<Refusal>> {
        let mut cause = vec![None; self.types.len()];
        let blame = self.blame.as_deref().unwrap_or_default();
        let forks: Vec<(usize, Refusal)> = blame
            .iter()
            .filter(|(_, r, _)| *r == Refusal::Fork)
            .map(|&(t, r, _)| (t, r))
            .collect();
        let mut rest: Vec<(usize, Refusal)> = blame
            .iter()
            .filter(|(_, r, _)| *r != Refusal::Fork)
            .map(|&(t, r, _)| (t, r))
            .collect();
        rest.sort_by_key(|&(_, r)| Self::refusal_rank(r));
        let mut stack = Vec::new();
        for (t, r) in forks.into_iter().chain(rest) {
            let is_fork = r == Refusal::Fork;
            if cause[t].is_some() || (!is_fork && (self.answer[t] || self.witnessed.contains(&t))) {
                continue;
            }
            cause[t] = Some(r);
            stack.push(t);
            while let Some(x) = stack.pop() {
                for &y in &self.readers[x] {
                    let propagates = if is_fork {
                        self.answer[x] || !self.answer[y]
                    } else {
                        !self.answer[y] && !self.witnessed.contains(&y)
                    };
                    if propagates && cause[y].is_none() {
                        cause[y] = Some(r);
                        stack.push(y);
                    }
                }
            }
        }
        cause
    }

    /// The answer for `t` when it is known: a type met before in this search, read by the type
    /// being decided, or one kept from an earlier search. Otherwise `t` is numbered, read by the
    /// type being decided and marked as being decided itself, and its number is given.
    fn met(&mut self, t: &Type) -> ControlFlow<bool, usize> {
        if let Some(&i) = self.ids.get(t) {
            if self.canonical_blame && !self.in_subtype_check && !self.canonical_ready[i] {
                self.canonical_ready[i] = true;
                self.again.insert(i);
            }
            if let Some(c) = self.current {
                let fresh = self.add_reader(i, c);
                if fresh {
                    let ep = self.epoch;
                    self.push_read(c, pack_read(i, true), ep);
                } else if self.canonical_blame {
                    let ep = self.epoch;
                    let packed = pack_read(i, true);
                    if self.reads[c].last() != Some(&(packed, ep)) {
                        self.push_read(c, packed, ep);
                    }
                }
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
        if self.canonical_blame {
            self.canonical_ready.push(!self.in_subtype_check);
        }
        if self.blame.is_some() {
            self.blamed_node.push(self.canonical_blame);
        }
        self.readers.push(BTreeSet::new());
        if let Some(c) = self.current {
            let ep = self.epoch;
            self.push_read(c, pack_read(i, true), ep);
        }
        self.reads.push(Vec::new());
        self.first_reads.push(DigestMap::default());
        self.deciding.insert(i);
        ControlFlow::Continue(i)
    }

    /// Whether the search or the decision of one of `ts` rests on a fork.
    // Complexity tradeoff (COMPLEXITY.md K102): the naive test walks the reads from each type
    // of `ts` alone and collects the forked types for each, O(|ts| (B log B + T + R)) for B
    // blamed, T types and R reads; one walk from all of `ts` with one visited set is
    // O(B log B + T + R). Given up: the walk is redone per call, so a caller that calls once
    // per value type pays that per call; `end_phase` marks every type once instead.
    fn rests_on_fork(&self, ts: impl IntoIterator<Item = usize>) -> bool {
        if self.refused == Some(Refusal::Fork) {
            return true;
        }
        let Some(blame) = self.blame.as_ref() else {
            return false;
        };
        if blame.forks == 0 {
            return false;
        }
        let forked: BTreeSet<usize> = blame
            .iter()
            .filter_map(|&(x, r, _)| (r == Refusal::Fork).then_some(x))
            .collect();
        let mut stack: Vec<usize> = ts.into_iter().filter(|&t| self.answer[t]).collect();
        let mut seen: HashSet<usize> = stack.iter().copied().collect();
        while let Some(x) = stack.pop() {
            if forked.contains(&x) {
                return true;
            }
            for &(packed, _) in &self.reads[x] {
                let (y, empty_dep) = unpack_read(packed);
                if empty_dep && self.answer[y] && seen.insert(y) {
                    stack.push(y);
                }
            }
        }
        false
    }

    /// For each type, whether its search or decision rests on a fork ([`Self::rests_on_fork`]):
    /// a type with answer `true` that reads as empty, through types with answer `true`, a forked
    /// type with answer `true`. One walk back over the reads from the forked types, O(B + T + R).
    fn fork_resting(&self) -> Vec<bool> {
        let n = self.types.len();
        if self.refused == Some(Refusal::Fork) {
            return vec![true; n];
        }
        let mut rest = vec![false; n];
        let Some(blame) = self.blame.as_ref() else {
            return rest;
        };
        if blame.forks == 0 {
            return rest;
        }
        let mut stack: Vec<usize> = Vec::new();
        for &(x, r, _) in blame.iter() {
            if r == Refusal::Fork && self.answer[x] && !rest[x] {
                rest[x] = true;
                stack.push(x);
            }
        }
        if stack.is_empty() {
            return rest;
        }
        let mut read_by: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (x, reads) in self.reads.iter().enumerate() {
            if self.answer[x] {
                for &(packed, _) in reads {
                    let (y, empty_dep) = unpack_read(packed);
                    if empty_dep {
                        read_by[y].push(x);
                    }
                }
            }
        }
        while let Some(y) = stack.pop() {
            for &x in &read_by[y] {
                if !rest[x] {
                    rest[x] = true;
                    stack.push(x);
                }
            }
        }
        rest
    }

    /// Takes as dead the empty types `v` rests on, unless one rests on a type still being
    /// decided: an empty type read is what a proof rests on, and an inhabited one is not. Every
    /// type waiting to be decided again was decided first ([`Searching::no_value`]), so each
    /// answer read here is a decision of this phase, not the `true` a phase starts from. A
    /// type already dead changes nothing, so the phase that settles it again does not start
    /// another: each new phase takes at least one more type as dead, which bounds their number.
    fn settle(&mut self, v: usize) {
        if self.dead.contains(&v) || self.rests_on_fork([v]) {
            return;
        }
        let (mut seen, mut stack) = (BTreeSet::from([v]), vec![v]);
        while let Some(x) = stack.pop() {
            for &(packed, _) in &self.reads[x] {
                let (y, empty_dep) = unpack_read(packed);
                if !empty_dep || !self.answer[y] {
                    continue;
                }
                if self.deciding.contains(&y) || self.again.contains(&y) || self.round.contains(&y)
                {
                    return;
                }
                if !self.dead.contains(&y) && seen.insert(y) {
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
    // Complexity tradeoff (COMPLEXITY.md K31): the naive version walks the list from each type
    // to its cycle or dead end, O(k) a type and Θ(n²) for the `n` lists `R_k` of
    // `nth_from_end(n)`. Used: the answer of every type on a walk is recorded (`cycles`), so each
    // chain is walked once, O(n log n) in all with the ordered map. Tradeoff: the map holds an
    // entry for each type walked while the search lives, O(n) memory.
    fn find_cycle(&mut self, t: &Type) -> Option<Cycle> {
        let (mut seen, mut path) = (BTreeMap::new(), Vec::new());
        let (mut x, mut steps) = (t.clone(), 0);
        let (mut stop, mut link, mut item, mut at) = (None, None, None, None);
        loop {
            if x != *t && matches!(self.cycles.get(&x), Some(None)) {
                for y in path {
                    self.cycles.insert(y, None);
                }
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
                if let Some(r) = at {
                    for y in path.drain(..=r as usize) {
                        self.cycles.insert(y, None);
                    }
                    return None;
                }
                at = Some(steps);
                stop = Some(s);
            }
            if *link.get_or_insert_with(|| l.clone()) != l
                || *item.get_or_insert_with(|| e.clone()) != e
            {
                for y in path.drain(..path.len() - 1) {
                    self.cycles.insert(y, None);
                }
                return None;
            }
            x = next;
            steps += 1;
            if x == *t {
                break;
            }
        }
        let c = Cycle {
            stop: stop?,
            link: link?,
            item: item?,
            period: steps,
            at: at?,
        };
        // Every type on the cycle is on the same cycle, `j` steps on, so its stop is `j` steps
        // nearer: each is recorded, and the members of one cycle asked in turn walk it once in
        // all, not once each.
        for (j, y) in (path.into_iter().enumerate()).skip(1) {
            let at = (c.at + c.period - j as u64 % c.period) % c.period;
            self.cycles.insert(y, Some(Cycle { at, ..c.clone() }));
        }
        Some(c)
    }

    /// Keeps `v` among the values shown, and gives its number.
    fn show(&mut self, v: Rep) -> usize {
        self.shown.push(v);
        self.shown.len() - 1
    }

    /// The value numbered `v` as a plain value ([`makeable`]) when it is one: a value of a plain
    /// kind, or a tuple of such values, read in place of `Searching::member_known` by
    /// `Searching::holds_known`. Each value is read once for the search, from a list rather
    /// than the thread's stack, the parts of a tuple first; values shown are never changed, and
    /// a tuple is shown after its parts.
    fn plain(&mut self, v: usize) -> Option<Value> {
        let mut todo = vec![v];
        while let Some(&w) = todo.last() {
            if self.plain.contains_key(&w) {
                todo.pop();
                continue;
            }
            let made = match &self.shown[w] {
                Rep::Value(x) => makeable(x).then(|| x.clone()),
                Rep::Tuple(vs) => {
                    let missing: Vec<usize> = (vs.iter().copied())
                        .filter(|p| !self.plain.contains_key(p))
                        .collect();
                    if !missing.is_empty() {
                        todo.extend(missing);
                        continue;
                    }
                    (vs.iter().map(|p| self.plain[p].clone()))
                        .collect::<Option<Vec<Value>>>()
                        .map(Value::tuple)
                }
                _ => None,
            };
            self.plain.insert(w, made);
            todo.pop();
        }
        self.plain[&v].clone()
    }

    /// The value numbered `v` as a value, for [`Type::witness`]: what [`Search::plain`] gives,
    /// and atoms and lists too, values of other searches read in ([`Search::local`]); `None`
    /// when it holds a closure or a struct. Each value is read once, from a list rather than
    /// the thread's stack, as in `plain`.
    // Complexity tradeoff: kept apart from `plain`, which `Searching::holds_known` reads in place
    // of a membership test, so the search's path and cost are as they were; `plain` alone gave
    // no value for any list, so `witness` gave none for an inhabited type of lists (the lists
    // of only 1s, BENCH-row-rep-many-tuples). A `Rep::List` is built link by link, linear in its
    // length, which the search keeps as a number since a meet of pure cycles can make it
    // exponential in the cycles; that length is the size of the value asked for. Read only by
    // `witness`, a query for tests.
    fn value(&mut self, v: usize) -> Option<Value> {
        let mut made: HashMap<usize, Option<Value>> = HashMap::new();
        // The values whose parts were pushed once: met again with a part still missing, that
        // part waits on it, a cycle (only a closure can close one, and a closure is a leaf
        // here, but nothing else rules it out), so it gives no value rather than loop.
        let mut entered: HashSet<usize> = HashSet::new();
        let mut todo = vec![v];
        while let Some(&w) = todo.last() {
            if made.contains_key(&w) {
                todo.pop();
                continue;
            }
            let at = self.local(w);
            let parts: Vec<usize> = match &self.shown[at] {
                Rep::Tuple(vs) => vs.clone(),
                Rep::Atom(_, p) => vec![*p],
                Rep::List { item, .. } => vec![*item],
                _ => vec![],
            };
            let missing: Vec<usize> = parts
                .iter()
                .copied()
                .filter(|p| !made.contains_key(p))
                .collect();
            if !missing.is_empty() {
                if entered.insert(w) {
                    todo.extend(missing);
                } else {
                    made.insert(w, None);
                    todo.pop();
                }
                continue;
            }
            let got = |p: usize| made[&p].clone();
            let x = match &self.shown[at] {
                Rep::Value(x) => Some(x.clone()),
                Rep::Tuple(vs) => (vs.iter().map(|&p| got(p)))
                    .collect::<Option<Vec<Value>>>()
                    .map(Value::tuple),
                Rep::Atom(name, p) => match got(*p) {
                    Some(Value::Tuple(items)) => {
                        Some(Value::atom_with(name.clone(), items.as_slice().to_vec()))
                    }
                    _ => None,
                },
                Rep::List {
                    stop,
                    link,
                    item,
                    len,
                } => match (got(*item), usize::try_from(len)) {
                    (Some(x), Ok(n)) => Some((0..n).fold(Value::atom(stop), |rest, _| {
                        Value::atom_with(link.clone(), vec![x.clone(), rest])
                    })),
                    _ => None,
                },
                Rep::Of { .. } | Rep::Closure(_) | Rep::Struct => None,
            };
            made.insert(w, x);
            todo.pop();
        }
        made.remove(&v).flatten()
    }

    /// The key of the value numbered `v` ([`Columns`]): the last value along its first
    /// components and its atoms' payloads (a payload being the tuple of an atom's arguments)
    /// when that is a scalar, a bare atom or the empty tuple, or `None` when the walk meets a
    /// value of another kind (a struct, a closure, a list, a path). A column type holds the
    /// value only if it lists the key ([`Reading::Payloads`]). Each value walked is given the
    /// key, so a value is walked once for the search; a value of another search is read in
    /// ([`Search::local`]), as `Searching::member_known` reads it.
    fn key(&mut self, v: usize) -> Option<Value> {
        let (mut path, mut w) = (Vec::new(), v);
        let key = loop {
            if let Some(k) = self.value_keys.get(&w) {
                break k.clone();
            }
            path.push(w);
            let local = self.local(w);
            match &self.shown[local] {
                Rep::Value(x) => break leaf(x),
                Rep::Tuple(vs) => match vs.first() {
                    Some(&c) => w = c,
                    None => break Some(Value::tuple(Vec::new())),
                },
                Rep::Atom(_, payload) => w = *payload,
                Rep::List { .. } | Rep::Of { .. } | Rep::Closure(_) | Rep::Struct => break None,
            }
        };
        for w in path {
            self.value_keys.insert(w, key.clone());
        }
        key
    }

    /// The class of the value numbered `v`: one number for it and every value equal to it,
    /// shown here or kept in `STORES` ([`ValueKey`]). It and each of its parts not yet given a
    /// class are given one, the parts first, on a list rather than the thread's stack. A value
    /// whose key a kept value has takes that value's class; another is given one of this
    /// search's own, numbered down from `usize::MAX`, which a value kept later with the same key
    /// does not take, so such a value may have two classes: its membership is then tested twice,
    /// never answered for another value.
    fn class(&mut self, v: usize) -> usize {
        let mut todo = vec![v];
        while let Some(&w) = todo.last() {
            if self.classes.contains_key(&w) {
                todo.pop();
                continue;
            }
            let missing: Vec<usize> = (self.shown[w].parts().into_iter())
                .filter(|p| !self.classes.contains_key(p))
                .collect();
            if !missing.is_empty() {
                todo.extend(missing);
                continue;
            }
            todo.pop();
            let class = match &self.shown[w] {
                Rep::Of { store, at, .. } => stored_class(*store, *at),
                Rep::Closure(_) => self.own_class(),
                r => {
                    let classes = &self.classes;
                    let key = r.key(|p| classes[&p]);
                    match CLASSES.with(|c| c.borrow().keys.get(&key).copied()) {
                        Some(class) => class,
                        None => match self.own_keys.get(&key) {
                            Some(&class) => class,
                            None => {
                                let class = self.own_class();
                                self.own_keys.insert(key, class);
                                class
                            }
                        },
                    }
                }
            };
            self.classes.insert(w, class);
        }
        self.classes[&v]
    }

    /// A class of this search's own ([`Search::class`]).
    fn own_class(&mut self) -> usize {
        self.own_classes += 1;
        usize::MAX - self.own_classes
    }

    /// The number of the value of another search at `at` in the list `store` of `STORES`.
    fn foreign(&mut self, store: usize, at: usize, of: Option<Type>) -> usize {
        if let Some(&v) = self.foreign.get(&(store, at)) {
            return v;
        }
        let v = self.show(Rep::Of { store, at, of });
        self.foreign.insert((store, at), v);
        v
    }

    /// The value numbered `v`, with its outer level read in when it is a value of another
    /// search: the same value, whose parts are values of that search ([`Search::foreign`]).
    /// Each is read in once, and only the levels a test reads are, so a search reads no more of
    /// a shared value than it would have built.
    fn local(&mut self, v: usize) -> usize {
        let Rep::Of { store, at, .. } = self.shown[v] else {
            return v;
        };
        if let Some(&e) = self.expanded.get(&v) {
            return e;
        }
        let (mut store, mut at) = (store, at);
        let rep = loop {
            match STORES.with(|s| s.borrow()[store][at].clone()) {
                Rep::Of {
                    store: s, at: a, ..
                } => (store, at) = (s, a),
                r => break r,
            }
        };
        let rep = match rep {
            Rep::Tuple(vs) => Rep::Tuple(
                vs.into_iter()
                    .map(|i| self.foreign(store, i, None))
                    .collect(),
            ),
            Rep::Atom(name, p) => Rep::Atom(name, self.foreign(store, p, None)),
            Rep::List {
                stop,
                link,
                item,
                len,
            } => Rep::List {
                stop,
                link,
                item: self.foreign(store, item, None),
                len,
            },
            r => r,
        };
        let e = self.show(rep);
        self.expanded.insert(v, e);
        e
    }

    /// Component `i` of the tuple numbered `v` among the values shown.
    fn tuple_item(&self, v: usize, i: usize) -> usize {
        match &self.shown[v] {
            Rep::Tuple(vs) => vs[i],
            // The one caller reads `v` under `Shape::Tuple`, made from `shown[v]` being a
            // `Rep::Tuple`, and `shown` is only pushed to while a search runs.
            _ => unreachable!("the value numbered {v} is read as a tuple and is not one"),
        }
    }

    /// The stop atom, link atom and length of the list numbered `v` among the values shown.
    fn list_parts(&self, v: usize) -> (&std::sync::Arc<str>, &std::sync::Arc<str>, &BigUint) {
        match &self.shown[v] {
            Rep::List {
                stop, link, len, ..
            } => (stop, link, len),
            // Read only by `list_member`, whose one caller passes `v` under `Shape::List`, made
            // from `shown[v]` being a `Rep::List`; `shown` is only pushed to while a search runs.
            _ => unreachable!("the value numbered {v} is read as a list and is not one"),
        }
    }

    /// The height of the value numbered `v` among the values shown, when every level of it is
    /// shown here: a scalar, a bare atom, a struct or a closure is of height 0, a tuple one more
    /// than its highest component (1 when it has none), an atom with a payload one more than its
    /// payload tuple. `None` for a value with a level not read in ([`Rep::Of`]), a list kept as
    /// its length ([`Rep::List`]) or a compound [`Value`]: [`Heights::least_height_node`] is compared
    /// only with a height known exactly. Each value is measured once, on a list rather than the
    /// thread's stack, so a list of `n` items costs `O(n)` once for all its suffixes.
    fn value_height(&mut self, v: usize) -> Option<u64> {
        let mut todo = vec![v];
        while let Some(&w) = todo.last() {
            if self.heights.contains_key(&w) {
                todo.pop();
                continue;
            }
            let missing: Vec<usize> = match &self.shown[w] {
                Rep::Tuple(_) | Rep::Atom(..) => (self.shown[w].parts().into_iter())
                    .filter(|p| !self.heights.contains_key(p))
                    .collect(),
                _ => Vec::new(),
            };
            if !missing.is_empty() {
                todo.extend(missing);
                continue;
            }
            todo.pop();
            let h = match &self.shown[w] {
                Rep::Value(x) => match x {
                    Value::Tuple(_) | Value::Path(_) => None,
                    Value::Atom(a) if !a.is_bare() => None,
                    _ => Some(0),
                },
                Rep::Struct | Rep::Closure(_) => Some(0),
                Rep::Tuple(vs) => vs
                    .iter()
                    .try_fold(0, |m, p| self.heights[p].map(|h| m.max(h)))
                    .map(|m| m + 1),
                Rep::Atom(_, p) => self.heights[p].map(|h| h + 1),
                Rep::List { .. } | Rep::Of { .. } => None,
            };
            self.heights.insert(w, h);
        }
        self.heights[&v]
    }
}

/// A node in the height-bounds DAG: either a [`Type`] or a shared persistent [`super::atoms::PayloadNode`]
/// representing the union of its subtree's payload-bearing atoms.
#[derive(Clone)]
enum HeightNode {
    Type(Type),
    Payloads(std::sync::Arc<super::atoms::PayloadNode>),
}

impl PartialEq for HeightNode {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (HeightNode::Type(a), HeightNode::Type(b)) => a == b,
            (HeightNode::Payloads(a), HeightNode::Payloads(b)) => a.id() == b.id(),
            _ => false,
        }
    }
}

impl Eq for HeightNode {}

impl std::hash::Hash for HeightNode {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            HeightNode::Type(t) => {
                0u8.hash(state);
                t.hash(state);
            }
            HeightNode::Payloads(n) => {
                1u8.hash(state);
                n.id().hash(state);
            }
        }
    }
}

/// The bounds on the heights of types' values ([`height_bounds`]), kept in `HEIGHTS`.
#[derive(Default)]
struct Heights {
    /// The least height of a value of each type asked about ([`Heights::least_height_node`]).
    least: HashMap<Type, u64, Digests>,
    /// The least and greatest height of a value of each type asked about, `None` for a type
    /// shown to have no value ([`Heights::height_bounds`]).
    bounds: HashMap<Type, Option<(u64, u64)>, Digests>,
    /// Cached least height and `(lo, hi)` bounds per shared [`super::atoms::PayloadNode::id`],
    /// so `n` prefix unions sharing persistent payload trees are bounded in `O(n log n)`.
    payload_least: DigestMap<u64, u64>,
    payload_bounds: DigestMap<u64, Option<(u64, u64)>>,
}

/// [`Heights::height_bounds`] of `t`, kept for every search of this thread until
/// `Type::forget_emptiness`: the bounds are a function of the type alone (their proof reads
/// nothing but `t` and the types it reaches), so a search reads those another made.
// Complexity tradeoff: each type is bounded once until the kept results are dropped, so the
// searches of a check together walk each type reached once, O(V + E) in all. Naive
// alternative: bounds kept per search, as they were until PERF-height-bounds-group-benches;
// each search walked again every type its first question reaches, and the searches of a group
// of n definitions that each reach O(n) types walked O(n^2) types: the X14 groups
// (`group_oracle::bench`, with the bounds asked of every type), 1,579 types walked at n 256 and
// 23,401 at n 1024; kept here, 213 and 860, and 3,473 at n 4096 (debug build: 8.48M, 45.1M,
// 397M instructions at n 64, 256, 1024 before; 7.19M, 53.6M, 424M at n 64, 512, 4096 after,
// 7.5 and 7.9 times a step). The map is taken out of `HEIGHTS` while a type is bounded, so a
// question asked while making a type's parts (unfolding a recursive node) bounds with an empty
// map and adds its answers back, rather than finding the map borrowed; what both found is
// merged, the smaller map into the larger.
fn height_bounds(t: &Type) -> Option<(u64, u64)> {
    if let Some(b) = HEIGHTS.with_borrow(|h| h.bounds.get(t).copied()) {
        return b;
    }
    let mut h = HEIGHTS.take();
    let b = h.height_bounds(t);
    HEIGHTS.with_borrow_mut(|kept| {
        // `kept` is empty unless a question was asked inside this one; the larger map stays.
        let kept_len = kept.bounds.len()
            + kept.least.len()
            + kept.payload_bounds.len()
            + kept.payload_least.len();
        let h_len = h.bounds.len() + h.least.len() + h.payload_bounds.len() + h.payload_least.len();
        if kept_len < h_len {
            std::mem::swap(kept, &mut h);
        }
        kept.bounds.extend(h.bounds);
        kept.least.extend(h.least);
        kept.payload_bounds.extend(h.payload_bounds);
        kept.payload_least.extend(h.payload_least);
    });
    b
}

impl Heights {
    fn get_least(&self, node: &HeightNode) -> Option<u64> {
        match node {
            HeightNode::Type(t) => self.least.get(t).copied(),
            HeightNode::Payloads(n) => self.payload_least.get(&n.id()).copied(),
        }
    }

    fn has_bounds(&self, node: &HeightNode) -> bool {
        match node {
            HeightNode::Type(t) => self.bounds.contains_key(t),
            HeightNode::Payloads(n) => self.payload_bounds.contains_key(&n.id()),
        }
    }

    /// A lower bound on the height ([`Search::value_height`]) of every value of `root`, `u64::MAX`
    /// when `root` has none: the height of the shortest derivation of `root` in the grammar whose
    /// rules are, for each type, a scalar, a bare atom, a struct or a closure it may hold (height
    /// 0); an atom name with a payload type `a` (one more than `a`, factored through shared
    /// [`super::atoms::PayloadNode`] union nodes of offset 0 so shared prefix maps cost
    /// `O(n log n)`); a tuple length it holds all of, or whose part is not false on a tuple in
    /// none of its tuple types (height 1); and each tuple type of a part false on a tuple in none
    /// of them (one more than its highest component).
    ///
    /// Proof that it is a lower bound: every value `x` of `t` is derived by such a rule of `t`
    /// from values of its child types, each of a smaller height, so by induction on the height of
    /// `x` each child value's height is at least its type's bound, and the rule gives `t` a
    /// derivation no higher than `x`. A tuple of a part false on a tuple in none of its tuple
    /// types is in one of them, since otherwise every tuple type is false of it and so is the
    /// part; it is then a value of that tuple type's components. A type left with no derivation
    /// has no value, so `u64::MAX` is a bound too.
    ///
    /// Each node's bound is kept in `HEIGHTS` ([`height_bounds`]); the nodes not yet bounded that
    /// `root` reaches are bounded together by Knuth's generalization of Dijkstra's algorithm
    /// (Knuth, "A generalization of Dijkstra's algorithm", Inf. Proc. Letters 6, 1977): each
    /// rule's height is `add` (0 or 1) plus the highest of its children's, a superior function,
    /// so the nodes are settled in order of height and each rule is ready once its last child is
    /// settled.
    // Complexity tradeoff: O(E log E) for the E rules and children of the types and shared
    // `PayloadNode`s reached and not bounded before, each once until the kept bounds are dropped.
    // Naive alternatives: iterating all `p.atoms.payloads()` per type costs `Theta(n^2 log n)`
    // time and `Theta(n^2)` bytes on `r11_payload_name_prefixes_must_scale`; iterating the
    // equations to a fixpoint from 0 has no bound on rounds when a cycle derives nothing.
    #[cfg(test)]
    fn least_height(&mut self, t: &Type) -> u64 {
        self.least_height_node(&HeightNode::Type(t.clone()))
    }

    fn least_height_node(&mut self, root: &HeightNode) -> u64 {
        if let Some(h) = self.get_least(root) {
            return h;
        }
        // A rule of `node`: `base` is `add` more than the highest child settled so far, `waiting`
        // the children not yet settled.
        struct Rule {
            node: usize,
            add: u64,
            base: u64,
            waiting: usize,
        }
        let mut index: HashMap<HeightNode, usize, Digests> = HashMap::default();
        let mut nodes: Vec<HeightNode> = Vec::new();
        let mut users: Vec<Vec<usize>> = Vec::new();
        let mut rules: Vec<Rule> = Vec::new();
        let mut ready: std::collections::BinaryHeap<std::cmp::Reverse<(u64, usize)>> =
            std::collections::BinaryHeap::new();
        index.insert(root.clone(), 0);
        nodes.push(root.clone());
        users.push(Vec::new());
        let mut next = 0;
        while next < nodes.len() {
            let n = next;
            next += 1;
            let cur = nodes[n].clone();
            let mut children: Vec<(u64, Vec<HeightNode>)> = Vec::new();
            match &cur {
                HeightNode::Type(ty) => {
                    let p = ty.p();
                    let lits = [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings];
                    if p.bools != 0
                        || p.structs
                        || p.atoms.cofinite()
                        || p.morphisms.is_leaf() != Some(false)
                        || lits.iter().any(|l| l.cofinite || !l.values.is_empty())
                    {
                        ready.push(std::cmp::Reverse((0, n)));
                    }
                    if p.tuples.rest {
                        ready.push(std::cmp::Reverse((1, n)));
                    }
                    if p.atoms.bare_names() > 0 {
                        ready.push(std::cmp::Reverse((0, n)));
                    }
                    if let Some(pr) = p.atoms.payload_dag() {
                        children.push((0, vec![HeightNode::Payloads(pr.clone())]));
                    }
                    for f in p.tuples.lens.values() {
                        if f.is_leaf() == Some(false) {
                            continue;
                        }
                        if f.eval3(&|_| Some(false)) == Some(false) {
                            children.extend(
                                f.distinct_atoms().iter().map(|r| {
                                    (1, r.iter().cloned().map(HeightNode::Type).collect())
                                }),
                            );
                        } else {
                            ready.push(std::cmp::Reverse((1, n)));
                        }
                    }
                }
                HeightNode::Payloads(u) => {
                    children.push((1, vec![HeightNode::Type(u.payload().clone())]));
                    if let Some(l) = u.left() {
                        children.push((0, vec![HeightNode::Payloads(l.clone())]));
                    }
                    if let Some(r) = u.right() {
                        children.push((0, vec![HeightNode::Payloads(r.clone())]));
                    }
                }
            }
            for (add, row) in children {
                let r = rules.len();
                let mut rule = Rule {
                    node: n,
                    add,
                    base: add,
                    waiting: 0,
                };
                for c in row {
                    match self.get_least(&c) {
                        Some(h) => rule.base = rule.base.max(h.saturating_add(add)),
                        None => {
                            let i = *index.entry(c.clone()).or_insert_with(|| {
                                nodes.push(c);
                                users.push(Vec::new());
                                nodes.len() - 1
                            });
                            users[i].push(r);
                            rule.waiting += 1;
                        }
                    }
                }
                if rule.waiting == 0 && rule.base != u64::MAX {
                    ready.push(std::cmp::Reverse((rule.base, n)));
                }
                rules.push(rule);
            }
        }
        let mut height = vec![u64::MAX; nodes.len()];
        while let Some(std::cmp::Reverse((h, n))) = ready.pop() {
            if height[n] != u64::MAX {
                continue;
            }
            height[n] = h;
            for &r in &users[n] {
                let rule = &mut rules[r];
                rule.base = rule.base.max(h.saturating_add(rule.add));
                rule.waiting -= 1;
                if rule.waiting == 0 && rule.base != u64::MAX && height[rule.node] == u64::MAX {
                    ready.push(std::cmp::Reverse((rule.base, rule.node)));
                }
            }
        }
        for (node, h) in nodes.into_iter().zip(height) {
            match node {
                HeightNode::Type(ty) => {
                    self.least.insert(ty, h);
                }
                HeightNode::Payloads(u) => {
                    self.payload_least.insert(u.id(), h);
                }
            }
        }
        self.get_least(root).expect("root settled above")
    }

    /// The nodes whose values' heights bound those of `node`'s values: for a `Type`, its shared
    /// [`super::atoms::PayloadNode`] root (if any) and each component of each tuple type of each
    /// tuple part; for a `PayloadNode`, its payload type and its left and right subtrees.
    // Complexity tradeoff (R11-C3): reading `p.atoms.payloads()` flat per type cost
    // `Theta(n^2 log n)` time and `Theta(n^2)` bytes on `r11_payload_name_prefixes_must_scale`.
    // Stepping through the persistent `PayloadNode` tree gives `O(1)` children per node and
    // visits each shared tree node once across all prefix types (`O(n log n)`).
    fn height_children(node: &HeightNode) -> Vec<HeightNode> {
        let mut out: Vec<HeightNode> = Vec::new();
        match node {
            HeightNode::Type(t) => {
                let p = t.p();
                if let Some(pr) = p.atoms.payload_dag() {
                    out.push(HeightNode::Payloads(pr.clone()));
                }
                for f in p.tuples.lens.values() {
                    for row in f.distinct_atoms() {
                        out.extend(row.iter().cloned().map(HeightNode::Type));
                    }
                }
            }
            HeightNode::Payloads(u) => {
                out.push(HeightNode::Type(u.payload().clone()));
                if let Some(l) = u.left() {
                    out.push(HeightNode::Payloads(l.clone()));
                }
                if let Some(r) = u.right() {
                    out.push(HeightNode::Payloads(r.clone()));
                }
            }
        }
        out
    }

    /// Bounds `(lo, hi)` on the height ([`Search::value_height`]) of every value of `t`, `hi`
    /// `u64::MAX` when none is known; `None` when `t` is shown to have no value. `lo` is
    /// [`Heights::least_height_node`]. `hi` is `u64::MAX` for a type on a cycle of the types it
    /// reaches through atom payloads and tuple components; for any other type it is the
    /// greatest over its parts: 0 for a scalar, a bare atom, a struct or a closure, `u64::MAX`
    /// for the atoms outside a finite set or the tuples of a length it holds all of, one more
    /// than the payload's `hi` for an atom with a payload, and for a tuple part one more than the
    /// greatest component bound over its clauses ([`Heights::part_heights`]). A type whose parts
    /// all have no value, or whose `lo` exceeds its `hi`, is `None`.
    ///
    /// Proof that the bounds hold, by induction on the order in which the types are bounded
    /// (each type after every type it reaches outside its own cycle): a value `x` of `t` is in
    /// one of its parts. A scalar, a bare atom, a struct or a closure has height 0. An atom with
    /// a payload `v` of the payload type has height `1 + h(v)`, within one more than that
    /// type's bounds, which exist since `v` is a value of it. A tuple of a part satisfies one of
    /// the part's clauses ([`Heights::part_heights`]), so each component lies in every tuple type
    /// the clause takes, and its height in the meet of their bounds at that component: that
    /// meet is not empty, the clause was kept, and `h(x)` is one more than the greatest
    /// component height, at most one more than the greatest kept upper bound. A type on a cycle
    /// is given `hi = u64::MAX`, which bounds anything. So `h(x) <= hi`, and `lo <= h(x)` by
    /// [`Heights::least_height_node`]; a type with no part left or with `lo > hi` has no value.
    ///
    /// Use: the meet of a list of length `a` and a list of length `b != a`, written as nested
    /// `#cons` tuples (`R_a`, of height exactly `2a`), has no value, and the search that
    /// shows it walks `min(a, b)` levels of new meets; here each meet of the lists' suffixes is
    /// bounded once in `O(1)` from the suffixes' bounds, kept for every search
    /// ([`height_bounds`]).
    // Complexity tradeoff: one walk of the types and shared `PayloadNode`s `t` reaches that are
    // not bounded yet, by Tarjan's algorithm for the cycles (Tarjan, "Depth-first search and
    // linear graph algorithms", SIAM J. Comput. 1, 1972), O(V + E) for the V nodes and E
    // children, plus each tuple part's clauses once, O(its literals times its length), plus
    // `least_height`, O(E log E); kept for every search ([`height_bounds`]). Naive alternative:
    // decide each meet by the search, which walks the shorter list once for each pair of lengths
    // met, O(n^2) types for `n` lengths (the lists by the place of a 1 from the end, `verdict`
    // at `n` 512: 263,783 types and 18.9 s; COMPLEXITY.md K126). Given up: a type on a cycle is
    // bounded from below only, so a meet of two cyclic types is left to the search; a part kept
    // as an expression is bounded through its tuple types as a union, or not at all.
    /// Bounds an acyclic `PayloadNode` whose `payload`, `left`, and `right` are already in
    /// `self.bounds` / `self.payload_bounds` in `O(1)` without launching Dijkstra.
    fn bound_acyclic_payload_node(&mut self, u: &super::atoms::PayloadNode) -> Option<(u64, u64)> {
        let mut lo = u64::MAX;
        let mut hi: Option<u64> = None;
        if let Some((pl, ph)) = self.bounds[u.payload()] {
            lo = lo.min(pl.saturating_add(1));
            let h = ph.saturating_add(1);
            hi = Some(hi.map_or(h, |x| x.max(h)));
        }
        if let Some(l) = u.left()
            && let Some((ll, lh)) = self.payload_bounds[&l.id()]
        {
            lo = lo.min(ll);
            hi = Some(hi.map_or(lh, |x| x.max(lh)));
        }
        if let Some(r) = u.right()
            && let Some((rl, rh)) = self.payload_bounds[&r.id()]
        {
            lo = lo.min(rl);
            hi = Some(hi.map_or(rh, |x| x.max(rh)));
        }
        self.payload_least.insert(u.id(), lo);
        let b = if lo == u64::MAX {
            None
        } else {
            hi.filter(|&h| lo <= h).map(|h| (lo, h))
        };
        self.payload_bounds.insert(u.id(), b);
        b
    }

    /// Fast path for a `PayloadTree` whose unseen nodes only reference `Type` payloads already
    /// present in `self.bounds`: bounds every unseen `PayloadNode` in one post-order walk with no
    /// Tarjan or Dijkstra allocations. Returns `true` when `root` is now in `self.payload_bounds`.
    fn bound_payload_tree_fast(&mut self, root: &super::atoms::PayloadNode) -> bool {
        if self.payload_bounds.contains_key(&root.id()) {
            return true;
        }
        let mut stack: Vec<(&super::atoms::PayloadNode, bool)> = vec![(root, false)];
        while let Some((node, ready)) = stack.pop() {
            if self.payload_bounds.contains_key(&node.id()) {
                continue;
            }
            if !ready {
                if !self.bounds.contains_key(node.payload()) {
                    return false;
                }
                stack.push((node, true));
                if let Some(r) = node.right()
                    && !self.payload_bounds.contains_key(&r.id())
                {
                    stack.push((r.as_ref(), false));
                }
                if let Some(l) = node.left()
                    && !self.payload_bounds.contains_key(&l.id())
                {
                    stack.push((l.as_ref(), false));
                }
            } else {
                self.bound_acyclic_payload_node(node);
            }
        }
        true
    }

    fn height_bounds(&mut self, t: &Type) -> Option<(u64, u64)> {
        if let Some(&b) = self.bounds.get(t) {
            return b;
        }
        if let Some(pr) = t.p().atoms.payload_dag() {
            self.bound_payload_tree_fast(pr);
        }
        // Tarjan's algorithm, on a list rather than the thread's stack. Each node reached and
        // not bounded is numbered in the order it is reached; `children[n]` are its children not
        // bounded, `low[n]` the least number reached from it on the stack, and a frame is a node
        // with the next of its children to visit.
        let mut index: HashMap<HeightNode, usize, Digests> = HashMap::default();
        let mut nodes: Vec<HeightNode> = Vec::new();
        let mut children: Vec<Vec<HeightNode>> = Vec::new();
        let mut low: Vec<usize> = Vec::new();
        let mut on_stack: Vec<bool> = Vec::new();
        let mut looped: Vec<bool> = Vec::new();
        let mut stack: Vec<usize> = Vec::new();
        let mut frames: Vec<(usize, usize)> = Vec::new();
        let mut reach = Some(HeightNode::Type(t.clone()));
        loop {
            if let Some(node) = reach.take() {
                let n = nodes.len();
                let cs: Vec<HeightNode> = (Self::height_children(&node).into_iter())
                    .filter(|c| !self.has_bounds(c))
                    .collect();
                looped.push(cs.contains(&node));
                index.insert(node.clone(), n);
                nodes.push(node);
                children.push(cs);
                low.push(n);
                on_stack.push(true);
                stack.push(n);
                frames.push((n, 0));
            }
            let Some(&mut (n, ref mut next)) = frames.last_mut() else {
                break;
            };
            if let Some(c) = children[n].get(*next) {
                *next += 1;
                match index.get(c) {
                    Some(&m) if on_stack[m] => low[n] = low[n].min(m),
                    Some(_) => {}
                    None => reach = Some(c.clone()),
                }
                continue;
            }
            frames.pop();
            if let Some(&(parent, _)) = frames.last() {
                low[parent] = low[parent].min(low[n]);
            }
            if low[n] != n {
                continue;
            }
            let mut scc = Vec::new();
            while let Some(m) = stack.pop() {
                on_stack[m] = false;
                scc.push(m);
                if m == n {
                    break;
                }
            }
            let cyclic = scc.len() > 1 || looped[n];
            for m in scc {
                let node = nodes[m].clone();
                if !cyclic && let HeightNode::Payloads(ref u) = node {
                    self.bound_acyclic_payload_node(u);
                    continue;
                }
                let lo = self.least_height_node(&node);
                let b = if lo == u64::MAX {
                    None
                } else if cyclic {
                    Some((lo, u64::MAX))
                } else {
                    self.most_height(&node)
                        .filter(|&hi| lo <= hi)
                        .map(|hi| (lo, hi))
                };
                match node {
                    HeightNode::Type(ty) => {
                        self.bounds.insert(ty, b);
                    }
                    HeightNode::Payloads(u) => {
                        self.payload_bounds.insert(u.id(), b);
                    }
                }
            }
        }
        self.bounds[t]
    }

    /// The greatest height over the parts of `node` ([`Heights::height_bounds`]), every node
    /// `node` reaches outside its own cycle bounded already; `None` when no part may hold a value.
    fn most_height(&mut self, node: &HeightNode) -> Option<u64> {
        let mut hi: Option<u64> = None;
        let mut take = |h: u64| hi = Some(hi.map_or(h, |x| x.max(h)));
        match node {
            HeightNode::Type(t) => {
                let p = t.p();
                let lits = [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings];
                if p.bools != 0
                    || p.structs
                    || p.morphisms.is_leaf() != Some(false)
                    || lits.iter().any(|l| l.cofinite || !l.values.is_empty())
                {
                    take(0);
                }
                if p.atoms.cofinite() || p.tuples.rest {
                    take(u64::MAX);
                }
                if p.atoms.bare_names() > 0 {
                    take(0);
                }
                if let Some(pr) = p.atoms.payload_dag()
                    && let Some((_, h)) = self.payload_bounds[&pr.id()]
                {
                    take(h);
                }
                for (&len, f) in &p.tuples.lens {
                    if let Some(v) = self.part_heights(len, f) {
                        let h = v.iter().map(|&(_, h)| h).max().unwrap_or(0);
                        take(h.saturating_add(1));
                    }
                }
            }
            HeightNode::Payloads(u) => {
                if let Some((_, h)) = self.bounds[u.payload()] {
                    take(h.saturating_add(1));
                }
                if let Some(l) = u.left()
                    && let Some((_, h)) = self.payload_bounds[&l.id()]
                {
                    take(h);
                }
                if let Some(r) = u.right()
                    && let Some((_, h)) = self.payload_bounds[&r.id()]
                {
                    take(h);
                }
            }
        }
        hi
    }

    /// Bounds on the height of each component of a tuple of the part `f` of length `len`, the
    /// widest over its clauses, `None` when every clause is shown to hold no tuple. On a
    /// decision list ([`Bdd::list`]) a tuple of the part takes a literal of a block of value
    /// `true`, or the tail when that is `true`, and refuses every literal of each block of value
    /// `false` before it; so it lies in the tuple type of that literal when it is taken, and in
    /// the tuple type of each literal refused that is not taken. The bounds of such a clause are
    /// the meet of those tuple types' bounds at each component, and a clause with an empty
    /// meet at some component holds no tuple. A part kept as an expression is bounded as the
    /// union of its tuple types when it holds no tuple outside them all, and is not bounded
    /// otherwise.
    // Complexity tradeoff: the tuple types refused through the blocks of value `false` are met
    // once as the list is read, so the clauses cost O(the list's literals times `len`) in all;
    // listing each clause's tuple types apart would cost the square of the blocks.
    fn part_heights(&mut self, len: usize, f: &Part<Row>) -> Option<Vec<(u64, u64)>> {
        let top = vec![(0, u64::MAX); len];
        let meet = |m: &mut Vec<(u64, u64)>,
                    row: &Row,
                    bounds: &HashMap<Type, Option<(u64, u64)>, Digests>|
         -> bool {
            for (j, c) in row.iter().enumerate() {
                match bounds[c] {
                    Some((lo, hi)) => {
                        m[j] = (m[j].0.max(lo), m[j].1.min(hi));
                        if m[j].0 > m[j].1 {
                            return false;
                        }
                    }
                    None => return false,
                }
            }
            true
        };
        let mut hull: Option<Vec<(u64, u64)>> = None;
        let mut join = |v: &[(u64, u64)]| match &mut hull {
            None => hull = Some(v.to_vec()),
            Some(h) => {
                for (x, y) in h.iter_mut().zip(v) {
                    *x = (x.0.min(y.0), x.1.max(y.1));
                }
            }
        };
        match f.view() {
            Ok(b) => {
                let list = b.list();
                let mut refused = top;
                let mut alive = true;
                'blocks: for (value, lits) in &list.blocks {
                    for (a, taken) in lits {
                        if *value {
                            if !*taken {
                                join(&refused);
                                continue;
                            }
                            let mut v = refused.clone();
                            if meet(&mut v, a, &self.bounds) {
                                join(&v);
                            }
                        } else if !*taken && !meet(&mut refused, a, &self.bounds) {
                            alive = false;
                            break 'blocks;
                        }
                    }
                }
                if alive && list.tail {
                    join(&refused);
                }
            }
            Err(_) => {
                if f.eval3(&|_| Some(false)) != Some(false) {
                    return Some(top);
                }
                for row in f.distinct_atoms() {
                    let mut v = top.clone();
                    if meet(&mut v, &row, &self.bounds) {
                        join(&v);
                    }
                }
            }
        }
        hull
    }
}

/// `roots`, and the types written in them outside a list: the components of their tuple rows,
/// the values of their morphisms, where the part is a union of literals, and the components of
/// their atoms' payloads but a list's own tail, and the same of those types in turn. The search
/// asks each of these of the root's tuple, record or atom part as it is written
/// (`Searching::parts`), so a list type in a root's field gets the prefix chains, the escape
/// solve and the front sweep as a root does.
// Complexity tradeoff: a walk of the roots' nodes with each node read once (`seen`), not
// entering a recursive node or a payload component with an atom of the payload's own name, so
// O(the nodes written above the roots' lists). Why: with the chains on the query's own types
// only (`prefix_chains`), a list type in a tuple or record field was left to the search:
// Refused or 100-1700 times the work on the probe cases put in a field (R8, Q5); in an atom's
// payload, `#wrap((l,))` was refused (R9, X42). Run on every list type the search meets
// instead, the chains cost `r6twowide` and `r6threeun` 45-65% more than main. A pair's first
// component that is a list of the same atom names (a list's item, X43) is walked and kept in
// `items`, still once per node, so the walk stays O(nodes); its tail (component 1) is not.
// Complexity tradeoff (R10-C4): "each node read once" was kept for type nodes only, and the
// rows of a tuple diagram were expanded again for each type that reads it, so K tags sharing
// one payload diagram of n rows cost K·n (refusals::r10_shared_payload_rows_must_scale). The
// rows of a payload diagram are now expanded once per (length, diagram id), split into the
// components with no atom name, queued once per context, and those with one; the own tuple and
// morphism diagrams are expanded once per (id, context). Given up: each tag still reads the
// named components of a shared payload, so a cost of K times the named components remains
// (refusals::r11_named_payload_probe, r11_tagged_payload_probe).
// Complexity tradeoff (R11-C4, Codex R11): exempting only a direct list item left the lists in
// its tuple or map fields to the fallback's searches (`listhead:pairfar` 641.9 times its bare
// case at 256). The item context is carried through the written fields: each node is visited
// at most twice, outside and inside an item, so O(nodes + edges) still.
///
/// Also the atom types among them that are not lists (`Search::wraps`): each payload of a
/// literal union of tuple rows with no link of a list in it.
fn fields(roots: &[Type]) -> (Vec<Type>, Vec<Type>, Vec<Type>) {
    let (mut seen, mut out, mut wraps, mut items) =
        (DigestSet::default(), Vec::new(), Vec::new(), Vec::new());
    // Named components in a payload diagram with one set of atom names (the same
    // `Atoms::names` `OrdMap` root, `OrdMap::ptr_eq`, or equal names), so a shared map of many
    // bare names is indexed once.
    struct NamedGroup {
        rep: Type,
        entries: Vec<(usize, Type)>,
    }
    // A payload diagram's distinct components with their place: those with no atom name
    // (`plain`) and those with one (`groups`, indexed by atom name in `by_name`), plus which
    // contexts have queued `plain` and which `groups` remain unpushed as non-matching.
    //
    // Complexity tradeoff (U3 / R10-C4): iterating `rows.named` per outer tag cost `Theta(K * W)`
    // when `K` outer tags share one payload diagram with `W` named components
    // (`r11_named_payload_probe`, `r11_tagged_payload_probe`). Grouping components by
    // `OrdMap::ptr_eq`, building an inverted index `by_name` once per diagram, and draining
    // non-matching `unpushed[ctx]` groups once per context reduces total work across all tags to
    // `O(W + sum |distinct maps| + total matches)`.
    struct Rows {
        plain: Vec<(usize, Type)>,
        groups: Vec<NamedGroup>,
        by_name: HashMap<std::sync::Arc<str>, Vec<usize>>,
        queued_plain: [bool; 2],
        unpushed: [Vec<usize>; 2],
        stamp: Vec<usize>,
        cur_stamp: usize,
    }
    // Payload diagrams read, by (length, diagram id), `None` when not a union of rows;
    // persistent `PayloadNode` wrap results + side effects memoized by `(PayloadNode::id, in_item)`;
    // tuple and morphism diagrams of the types themselves walked, by (id, context); list tails
    // followed by the X44 walk, by (node id, link name).
    let mut payloads: DigestMap<(usize, u64), Option<Rows>> = DigestMap::default();
    let mut payload_wrap: DigestMap<(u64, bool), bool> = DigestMap::default();
    let mut entry_wrap: DigestMap<(u64, bool), bool> = DigestMap::default();
    let (mut own, mut maps) = (DigestSet::default(), DigestSet::default());
    // Keyed by the program's link names, so it keeps the seeded hasher (`DigestMap` says why).
    let mut tails_seen = HashSet::new();
    let mut stack: Vec<(Type, bool)> = roots.iter().rev().map(|t| (t.clone(), false)).collect();
    while let Some((t, in_item)) = stack.pop() {
        if !seen.insert((t.node_id(), in_item)) {
            continue;
        }
        if !seen.contains(&(t.node_id(), !in_item)) {
            out.push(t.clone());
        }
        if in_item {
            items.push(t.clone());
        }
        let Node::Parts(p, _) = &*t.0 else {
            continue;
        };
        // An atom's payload components, but not one with an atom of the same name: that is a
        // link of a list through the atom (a cons cell's tail), whose walk would make every tail
        // of the list a root.
        // Complexity tradeoff (R11-C3): walking `p.atoms.payloads()` flat per type cost
        // `Theta(n^2 log n)` on `n` prefix unions sharing one persistent map
        // (`r11_payload_name_prefixes_must_scale`). Memoizing each `(PayloadNode::id, in_item)` in
        // `payload_wrap` and each shared `(PayloadEntry::id, in_item)` in `entry_wrap` visits
        // every shared tree node once and evaluates every distinct entry once per context
        // (`O(n log n)`).
        let mut wrap = !p.atoms.names().is_empty();
        if let Some(root) = p.atoms.payload_dag() {
            let mut pstack: Vec<(&super::atoms::PayloadNode, bool)> = vec![(root.as_ref(), false)];
            while let Some((node, ready)) = pstack.pop() {
                let key = (node.id(), in_item);
                if !ready {
                    if payload_wrap.contains_key(&key) {
                        continue;
                    }
                    pstack.push((node, true));
                    if let Some(r) = node.right()
                        && !payload_wrap.contains_key(&(r.id(), in_item))
                    {
                        pstack.push((r.as_ref(), false));
                    }
                    if let Some(l) = node.left()
                        && !payload_wrap.contains_key(&(l.id(), in_item))
                    {
                        pstack.push((l.as_ref(), false));
                    }
                    continue;
                }
                if payload_wrap.contains_key(&key) {
                    continue;
                }
                let mut node_wrap = true;
                if let Some(l) = node.left() {
                    node_wrap &= payload_wrap[&(l.id(), in_item)];
                }
                if let Some(r) = node.right() {
                    node_wrap &= payload_wrap[&(r.id(), in_item)];
                }
                let ekey = (node.entry_id(), in_item);
                let ew = if let Some(&w) = entry_wrap.get(&ekey) {
                    w
                } else if node.bare() {
                    entry_wrap.insert(ekey, true);
                    true
                } else {
                    let mut ew = true;
                    let name = node.name();
                    let pp = node.payload().p();
                    ew &= !pp.tuples.rest && !pp.structs;
                    for (len, b) in &pp.tuples.lens {
                        let rows = payloads.entry((*len, b.id())).or_insert_with(|| {
                            let mut plain = Vec::new();
                            let mut groups: Vec<NamedGroup> = Vec::new();
                            let mut group_buckets: DigestMap<(u64, u64, usize), Vec<usize>> =
                                DigestMap::default();
                            let mut met = DigestSet::default();
                            for row in b.union_rows()? {
                                for (i, c) in row.iter().enumerate() {
                                    if !met.insert((i, c.node_id())) {
                                        continue;
                                    }
                                    let cp = c.p();
                                    if cp.atoms.names().is_empty() {
                                        plain.push((i, c.clone()));
                                    } else {
                                        let bkey = (
                                            cp.atoms.sum(),
                                            cp.atoms.name_sum(),
                                            cp.atoms.names().len(),
                                        );
                                        let bucket = group_buckets.entry(bkey).or_default();
                                        // One group per set of atom names: a group is read
                                        // only for its rep's names (`by_name` below), so maps
                                        // of equal names built apart join one group.
                                        // Complexity tradeoff: grouping by `ptr_eq` alone put n
                                        // components whose equal maps were built apart (n
                                        // payloads `#a(x: i, f: (int) -> int)`) in n groups of
                                        // one bucket, and each scanned the bucket: n² steps
                                        // (kinds::bench, 44 times the work at 8n). With the
                                        // names compared too, a bucket holds one group per set
                                        // of names, and sets that differ share a bucket only
                                        // when their 64-bit sums collide, so each component
                                        // costs O(its names) expected, the walk O(nodes + names).
                                        let found = bucket.iter().copied().find(|&g| {
                                            let names = groups[g].rep.p();
                                            let names = names.atoms.names();
                                            names.ptr_eq(cp.atoms.names())
                                                || names.keys().eq(cp.atoms.names().keys())
                                        });
                                        let g = match found {
                                            Some(g) => g,
                                            None => {
                                                let g = groups.len();
                                                groups.push(NamedGroup {
                                                    rep: c.clone(),
                                                    entries: Vec::new(),
                                                });
                                                bucket.push(g);
                                                g
                                            }
                                        };
                                        groups[g].entries.push((i, c.clone()));
                                    }
                                }
                            }
                            let mut by_name: HashMap<std::sync::Arc<str>, Vec<usize>> =
                                HashMap::new();
                            for (g, group) in groups.iter().enumerate() {
                                for atom_name in group.rep.p().atoms.names().keys() {
                                    by_name.entry(atom_name.clone()).or_default().push(g);
                                }
                            }
                            let n_groups = groups.len();
                            Some(Rows {
                                plain,
                                groups,
                                by_name,
                                queued_plain: [false; 2],
                                unpushed: [(0..n_groups).collect(), (0..n_groups).collect()],
                                stamp: vec![0; n_groups],
                                cur_stamp: 0,
                            })
                        });
                        let Some(rows) = rows else {
                            ew = false;
                            continue;
                        };
                        // A pair's first component is a list's item, never its link (`list_step`
                        // reads the link at component 1); it and the fields written in it are in
                        // an item.
                        let pair = *len == 2;
                        let ctx = usize::from(in_item);
                        if !std::mem::replace(&mut rows.queued_plain[ctx], true) {
                            for (i, c) in &rows.plain {
                                stack.push((c.clone(), in_item || (pair && *i == 0)));
                            }
                        }
                        if let Some(matching) = rows.by_name.get(name) {
                            ew = false;
                            if !rows.unpushed[ctx].is_empty() {
                                rows.cur_stamp += 1;
                                let st = rows.cur_stamp;
                                for &g in matching {
                                    rows.stamp[g] = st;
                                }
                                let mut still = Vec::new();
                                for g in std::mem::take(&mut rows.unpushed[ctx]) {
                                    if rows.stamp[g] == st {
                                        still.push(g);
                                    } else {
                                        for (i, c) in &rows.groups[g].entries {
                                            let item = pair && *i == 0;
                                            stack.push((c.clone(), in_item || item));
                                        }
                                    }
                                }
                                rows.unpushed[ctx] = still;
                            }
                            for &g in matching {
                                for (i, c) in &rows.groups[g].entries {
                                    let item = pair && *i == 0;
                                    if item {
                                        // An item that is itself a list of the same names is
                                        // walked as a field (X43).
                                        items.push(c.clone());
                                        stack.push((c.clone(), true));
                                    } else if pair {
                                        // The tail: follow its literal links, each (node, link
                                        // name) once, and admit only a Boolean list type met on
                                        // the way (X44, at any depth); literal intermediate tails
                                        // are not roots.
                                        let mut tails = vec![c.clone()];
                                        while let Some(tail) = tails.pop() {
                                            if !tails_seen.insert((tail.node_id(), name.clone())) {
                                                continue;
                                            }
                                            if boolean_tail(&tail, name) {
                                                items.push(tail.clone());
                                                stack.push((tail, true));
                                            } else if let Some((_, link, _, next)) =
                                                list_step(&tail)
                                                && link == *name
                                            {
                                                tails.push(next);
                                            }
                                        }
                                    }
                                }
                            }
                        } else if !rows.unpushed[ctx].is_empty() {
                            for g in std::mem::take(&mut rows.unpushed[ctx]) {
                                for (i, c) in &rows.groups[g].entries {
                                    let item = pair && *i == 0;
                                    stack.push((c.clone(), in_item || item));
                                }
                            }
                        }
                    }
                    entry_wrap.insert(ekey, ew);
                    ew
                };
                node_wrap &= ew;
                payload_wrap.insert(key, node_wrap);
            }
            wrap &= payload_wrap[&(root.id(), in_item)];
        }
        if wrap {
            wraps.push(t.clone());
        }
        for b in p.tuples.lens.values() {
            if own.insert((b.id(), in_item)) {
                for row in b.union_rows().unwrap_or_default() {
                    stack.extend(row.iter().map(|c| (c.clone(), in_item)));
                }
            }
        }
        if maps.insert((p.morphisms.id(), in_item)) {
            for m in p.morphisms.union_rows().unwrap_or_default() {
                stack.push((m.value.clone(), in_item));
            }
        }
    }
    (out, wraps, items)
}

/// Whether `c`, the tail of a pair under the atom `name`, is a Boolean list type: its own pair
/// part under `name` is not a union of literal rows (a difference or a meet was written in it,
/// X44). Such a tail is walked as a root; a tail written as a union of rows (the next link of a
/// list) is not, so the walk does not make every tail of a written list a root.
// Complexity tradeoff: this boundary test is unchanged; the fields walk now follows
// literal links with its own visited set, so a Boolean boundary several links down is
// admitted without admitting every literal intermediate tail as a separate sweep root.
fn boolean_tail(c: &Type, name: &str) -> bool {
    let p = c.p();
    let Some(a) = p.atoms.names().get(name) else {
        return false;
    };
    a.payload
        .p()
        .tuples
        .lens
        .get(&2)
        .is_some_and(|b| b.union_rows().is_none())
}

/// The key of the value `x` ([`Search::key`]): the last value along its first components and
/// its atoms' tuple payloads, when that is a scalar, a bare atom or the empty tuple; `None` when
/// the walk meets an atom with a struct payload, a path or a function.
fn leaf(x: &Value) -> Option<Value> {
    let mut x = x;
    loop {
        let next = match x {
            Value::Tuple(items) => items.as_slice().first(),
            Value::Atom(a) => match &a.payload {
                None => return Some(x.clone()),
                Some(args) if a.fields.is_empty() => match args.as_slice().first() {
                    Some(c) => Some(c),
                    None => return Some(Value::tuple(Vec::new())),
                },
                Some(_) => return None,
            },
            Value::Path(_) | Value::Family(_) => return None,
            Value::Bool(_) | Value::Int(_) | Value::Big(_) | Value::Rat(_) => {
                return Some(x.clone());
            }
            Value::Float(_) | Value::Float32(_) | Value::Str(_) => return Some(x.clone()),
        };
        match next {
            Some(c) => x = c,
            None => return Some(x.clone()),
        }
    }
}

/// The rows of a tuple part filed by the keys their columns may hold, for a tuple some of whose
/// components are not plain ([`Search::plain`]). A component's key is the last value along its
/// first components and its atoms' payloads ([`Search::key`]); a column type whose every value
/// with a key has one of the type's keys ([`Reading::Payloads`]) is listed, and holds a
/// component only if it lists the component's key. So a row is tested only when, at a chosen
/// component with a key, its column lists that key or is not listed. The part's value is read
/// from the rows that hold, by evaluating again only the nodes they change
/// ([`Graph`](super::Graph)).
struct Columns {
    /// The distinct rows of the part, sorted.
    rows: Vec<Row>,
    /// Per column, each key with the key sets that list it, by position in `sets`.
    by: Vec<BTreeMap<Value, Vec<usize>>>,
    /// Per key set of a column, the rows whose column has it, ascending.
    sets: Vec<Vec<usize>>,
    /// Per column, the rows whose column is not listed, ascending.
    open: Vec<Vec<usize>>,
    graph: super::Graph,
    /// Each node's value with every row false.
    base: super::Base,
}

impl Columns {
    // Complexity tradeoff: rows whose column types share one key set ([`Filer`] shares the set
    // of a type with the types whose keys are all its own) are filed once under its keys, the
    // set read once per column, so filing costs the rows plus the distinct sets' keys,
    // O((r + k) log k). Naive version (the scalar filing of FAIL-kernel-empty-tuple-diff-union):
    // each row filed under each key of its column, O(r k log k), quadratic where r rows share a
    // column of k ≈ r literals. Cost: a query sums the sizes of the sets listing its key.
    fn new(len: usize, f: &Part<Row>, filer: &mut Filer) -> Columns {
        let mut rows = f.distinct_atoms();
        rows.sort();
        let mut by = vec![BTreeMap::<Value, Vec<usize>>::new(); len];
        let mut sets: Vec<Vec<usize>> = Vec::new();
        let mut open = vec![Vec::new(); len];
        // Per column, each key set filed by its address, with the set itself, held so that no
        // address is reused while filing.
        type Ids = HashMap<*const Vec<Value>, (std::rc::Rc<Vec<Value>>, usize)>;
        let mut ids: Vec<Ids> = (0..len).map(|_| Ids::new()).collect();
        for (i, row) in rows.iter().enumerate() {
            for (j, t) in row.iter().enumerate() {
                let filed = filer.file(t, Reading::Payloads);
                if !filed.listed {
                    open[j].push(i);
                    continue;
                }
                let at = std::rc::Rc::as_ptr(&filed.keys);
                let id = match ids[j].get(&at) {
                    Some(&(_, id)) => id,
                    None => {
                        let id = sets.len();
                        sets.push(Vec::new());
                        for k in filed.keys.iter() {
                            by[j].entry(k.clone()).or_default().push(id);
                        }
                        ids[j].insert(at, (filed.keys, id));
                        id
                    }
                };
                sets[id].push(i);
            }
        }
        let graph = super::Graph::new(&rows, f);
        let base = graph.base(|_| false);
        Columns {
            rows,
            by,
            sets,
            open,
            graph,
            base,
        }
    }

    /// The positions of the rows that may hold a tuple whose components have the keys `keys`
    /// where they are `Some`, ascending: of the component that leaves the fewest, the rows of
    /// the key sets listing its key and the open rows of its column. Every other row has a
    /// column that does not hold its component.
    // Assumption, not proved: a value in a column type that `Filer` files as listed under
    // `Reading::Payloads` has its key among that type's keys. Argued by induction along the
    // walk to the key: a scalar or bare atom is in a type only where its literal set or its
    // name's `bare` lists it, and cofinite sets or names leave the type unlisted; a tuple is in
    // a listed part only through a row, whose first column then holds its first component; an
    // atom with a tuple payload only through its name's payload type, which `Atoms::payloads`
    // names unless it lists nothing; and `Filer` gives a type the union of the keys it reaches,
    // listed only when all are. Evidence: the test
    // `a_value_in_a_listed_column_type_has_a_key_the_type_lists`, red with the payload types
    // left unread; and the answers of the tests of `types::empty`, unchanged.
    fn candidates(&self, keys: &[Option<Value>]) -> Vec<usize> {
        let at = |j: usize, k: &Value| {
            let sets = self.by[j].get(k).map_or(&[][..], Vec::as_slice);
            let count: usize = sets.iter().map(|&s| self.sets[s].len()).sum();
            (count + self.open[j].len(), sets, self.open[j].as_slice())
        };
        let (_, sets, open) = (keys.iter().enumerate())
            .filter_map(|(j, k)| Some(at(j, k.as_ref()?)))
            .min_by_key(|(count, _, _)| *count)
            .expect("a component has a key");
        let mut out: Vec<usize> = (sets.iter().flat_map(|&s| &self.sets[s]))
            .chain(open)
            .copied()
            .collect();
        out.sort_unstable();
        out
    }

    /// The part's value when the rows at `holding` hold and every other row does not.
    fn value(&self, holding: &[(usize, bool)]) -> bool {
        let none = super::Overlay::default();
        let over = self.graph.apply(&self.base, &none, holding);
        self.graph.root(&self.base, &none, &over)
    }
}

impl<'m> Searching<'m> {
    /// The search's state, for one statement or a scope with no `await` in it.
    fn s(&self) -> RefMut<'m, Search> {
        self.s.borrow_mut()
    }

    /// Decides each of `roots`: phases, in each of which an answer only goes from empty to
    /// inhabited; at the end of a phase each inhabited answer is tried for a checked value, and
    /// if a new one is found the answers without one start again from empty, so a wrong
    /// "inhabited" read by another decision is undone. The last phase gives the answers. The
    /// roots are walked in order, and every type met from any of them is decided in the same
    /// phases, once.
    async fn solve(&'m self, roots: &[Type]) -> Vec<bool> {
        // A value built from the tuple types as written answers at once, and no box is split.
        // Answers read on the way are unfinished, so none is kept. A type with no atoms has no
        // list to walk, and a row tested against every row would cost their square.
        let mut answers: Vec<Option<bool>> = vec![None; roots.len()];
        let mut seeded = false;
        let (written, wraps, items) = fields(roots);
        {
            let mut s = self.s();
            s.roots.extend(written.into_iter().map(|r| (r, ())));
            s.wraps.extend(wraps.into_iter().map(|r| (r, ())));
            s.items.extend(items.into_iter().map(|r| (r, ())));
        }
        for (a, root) in answers.iter_mut().zip(roots) {
            // A root read as a meet of parity lists and found empty is answered here, before a
            // value is tried for it: that would test each of its rows against every row, the
            // square of its operands (`affine_lists_empty`). Only roots are read, so a search
            // reads each list once.
            if affine_lists_empty(root) == Some(true) {
                *a = Some(true);
                continue;
            }
            if root.p().atoms.names().is_empty() {
                continue;
            }
            seeded = true;
            self.s().seeding = true;
            let seed = self.rep(root).await.is_some();
            self.s().seeding = false;
            if seed {
                *a = Some(false);
            }
        }
        if answers.iter().all(Option::is_some) {
            let mut s = self.s();
            s.types.clear();
            s.answer.clear();
            s.canonical_ready.clear();
            s.blamed_node.clear();
            return answers.into_iter().flatten().collect();
        }
        if seeded {
            self.s().forget_failures();
        }
        self.s().walking = true;
        let mut ids = vec![None; roots.len()];
        for ((a, id), root) in answers.iter_mut().zip(&mut ids).zip(roots) {
            if a.is_none() {
                *a = Some(self.empty(root).await);
                *id = self.s().ids.get(root).copied();
            }
        }
        self.s().walking = false;
        let answers: Vec<bool> = answers.into_iter().flatten().collect();
        if ids.iter().all(Option::is_none) {
            return answers;
        }
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
                    let mut s = self.s();
                    s.witnessed.insert(t);
                    if let Some(b) = s.blamed_node.get_mut(t) {
                        *b = false;
                    }
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
            if self.s().end_phase(open, new) {
                let s = self.s();
                return (answers.iter().zip(&ids))
                    .map(|(&b, id)| id.map_or(b, |r| s.answer[r]))
                    .collect();
            }
        }
    }

    async fn settle_canonical_blame(&'m self, roots: Vec<Type>) {
        {
            let mut guard = self.s();
            let s = &mut *guard;
            s.canonical_blame = true;
            s.walking = false;
            s.settled = false;
            s.deciding.clear();
            s.again.clear();
            s.round.clear();
            let mut reset = vec![false; s.types.len()];
            s.canonical_ready = vec![true; s.types.len()];
            let rest = s.fork_resting();
            for t in 0..s.types.len() {
                if s.answer[t] {
                    if !rest[t] {
                        s.dead.insert(t);
                    }
                } else if s.witnessed.contains(&t) {
                    s.answer[t] = false;
                    s.blamed_node[t] = false;
                } else {
                    reset[t] = true;
                    s.canonical_ready[t] = false;
                }
            }
            if let Some(blame) = &mut s.blame {
                blame.retain(|&(x, _, _)| x >= reset.len() || !reset[x]);
            }
            for (t, &r) in reset.iter().enumerate() {
                if r {
                    for (packed, _) in s.take_reads(t) {
                        let (u, _) = unpack_read(packed);
                        s.readers[u].remove(&t);
                    }
                    s.answer[t] = false;
                    s.blamed_node[t] = true;
                }
            }
            s.canonical_roots.clear();
            for root in &roots {
                if let Some(&id) = s.ids.get(root) {
                    s.canonical_roots.insert(id);
                    if !s.canonical_ready[id] {
                        s.canonical_ready[id] = true;
                        s.again.insert(id);
                    }
                }
            }
        }
        self.drain().await;
    }

    /// Decides again, in rounds, each type an answer it read has changed under. The round under
    /// way is kept in the search (`round`), so a drain started inside a decision decides the
    /// types still waiting in it before any answer is settled on ([`Searching::no_value`]); and a
    /// type being decided again is among those being decided (`deciding`), so no type is settled
    /// on its answer while it may still change. Taking `again` whole into the drain's own list
    /// hid both: a type of a later phase, `true` again until decided, was settled empty on that
    /// answer (plan item EMPTY-nonstrict-unsound).
    async fn drain(&'m self) {
        loop {
            let (t, fresh) = {
                let mut guard = self.s();
                let s = &mut *guard;
                if s.round.is_empty() {
                    s.round = std::mem::take(&mut s.again);
                }
                let Some(t) = s.round.pop_first() else {
                    return;
                };
                if s.canonical_blame && !s.canonical_roots.contains(&t) && s.readers[t].is_empty() {
                    s.canonical_ready[t] = false;
                    continue;
                }
                let done = if s.canonical_blame {
                    !s.answer[t] && !s.blamed_node[t]
                } else {
                    !s.answer[t]
                };
                if done {
                    continue;
                }
                (t, s.deciding.insert(t))
            };
            self.decide(t).await;
            if fresh {
                self.s().deciding.remove(&t);
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
        let (outer, ty, prev_level) = {
            let mut guard = self.s();
            let s = &mut *guard;
            let prev_level: u8 = if s.answer[t] {
                0
            } else if s.blamed_node.get(t).copied().unwrap_or(false) {
                1
            } else {
                2
            };
            if !s.canonical_blame
                && let Some(b) = s.blamed_node.get_mut(t)
            {
                *b = false;
            }
            if let Some(blame) = &mut s.blame {
                blame.retain(|&(x, _, _)| x != t);
            }
            for (packed, _) in s.take_reads(t) {
                let (u, _) = unpack_read(packed);
                s.readers[u].remove(&t);
            }
            (s.current.replace(t), s.types[t].clone(), prev_level)
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
                // `l01_23_groups_and_refusals::refusals::each_refusal_names_its_cause` (`erdos_cover`) and
                // `covering_residues_are_decided_by_a_split_on_one_prime`. COMPLEXITY.md K34 and
                // the Kept row "emptiness and subtyping of tuple and morphism parts". A complete
                // solution needs a backtracking split over several primes at once, exponential in
                // the primes, or a SAT encoding of the cover.
                self.s().give_up(Refusal::Residues);
                false
            }
            None => {
                if let Some(r) = self.swept(&ty) {
                    if r.is_some() {
                        self.s().witnessed.insert(t);
                    }
                    r.is_none()
                } else if self.in_fallback(&ty) {
                    self.parts(&ty.p()).await
                } else {
                    match self.prefix_chains(&ty).await {
                        Some(ChainPlan::Empty) => true,
                        Some(plan @ ChainPlan::Inhabited { .. }) => {
                            if self.chain_rep(&ty, plan).await.is_some() {
                                self.s().witnessed.insert(t);
                                false
                            } else {
                                self.s().chains.insert(ty.clone(), None);
                                let is_atom_list = !ty.p().atoms.names().is_empty()
                                    && !self.s().wraps.contains_key(&ty);
                                if is_atom_list {
                                    self.s().in_list_fallback += 1;
                                }
                                let res = self.parts(&ty.p()).await;
                                if is_atom_list {
                                    self.s().in_list_fallback -= 1;
                                }
                                res
                            }
                        }
                        None => {
                            let is_atom_list = !ty.p().atoms.names().is_empty()
                                && !self.s().wraps.contains_key(&ty);
                            if is_atom_list {
                                self.s().in_list_fallback += 1;
                            }
                            let res = self.parts(&ty.p()).await;
                            if is_atom_list {
                                self.s().in_list_fallback -= 1;
                            }
                            res
                        }
                    }
                }
            }
        };
        let mut guard = self.s();
        let s = &mut *guard;
        s.current = outer;
        if !b {
            s.answer[t] = false;
            if s.blame.is_some() {
                let has_blame = if s.witnessed.contains(&t) {
                    false
                } else {
                    let direct = s
                        .blame
                        .as_deref()
                        .is_some_and(|bl| bl.iter().any(|&(x, _, _)| x == t));
                    // The empty reads are tested for a fork in one walk ([`Search::rests_on_fork`]).
                    let child =
                        s.reads[t].iter().any(|&(packed, _)| {
                            let (u, empty_dep) = unpack_read(packed);
                            (!s.answer[u] && !s.witnessed.contains(&u) && s.blamed_node[u])
                                || (s.answer[u] && !empty_dep && !s.dead.contains(&u))
                        }) || s.rests_on_fork(s.reads[t].iter().filter_map(|&(packed, _)| {
                            let (u, empty_dep) = unpack_read(packed);
                            empty_dep.then_some(u)
                        }));
                    direct || child
                };
                s.blamed_node[t] = has_blame;
                if s.canonical_blame {
                    let new_level: u8 = if has_blame { 1 } else { 2 };
                    if new_level > prev_level {
                        s.again.extend(s.readers[t].iter().copied());
                    }
                } else {
                    s.again.extend(s.readers[t].iter().copied());
                }
            } else {
                s.again.extend(s.readers[t].iter().copied());
            }
        }
        b
    }

    /// For a search that takes `Refused`, the emptiness of `t` read off its verdict when `t` is a
    /// member of a group its decider leaves open and that group is not the one being decided:
    /// the group's one search ([`group_verdicts`]) decides it, once for every type that reads
    /// it, where each reader's search would decide again the part of the group it reaches. A
    /// verdict is a function of the group, so the answer read is the same whichever type asks
    /// first. A member refused for a fork refuses the reader as a fork met here does; one
    /// refused for another cause counts as inhabited with nothing shown, under that cause.
    fn group_verdict(&'m self, t: &Type) -> Option<bool> {
        if !t.is_member() || !self.s().strict || DECIDING.with(|d| d.borrow().contains(t)) {
            return None;
        }
        let r = match t.verdict() {
            Verdict::Empty => return Some(true),
            Verdict::Inhabited => return Some(false),
            Verdict::Refused(r) => r,
        };
        let mut guard = self.s();
        let s = &mut *guard;
        match r {
            Refusal::Fork if s.refuse_forks && !s.seeding => {
                let ep = s.epoch;
                match (&mut s.blame, s.current) {
                    (Some(blame), Some(c)) if s.trials.is_none_or(|n| n > 0) => {
                        blame.push((c, Refusal::Fork, ep))
                    }
                    _ => s.refused = Some(Refusal::Fork),
                }
                Some(true)
            }
            Refusal::NoWitness => Some(false),
            r => {
                s.give_up(r);
                Some(false)
            }
        }
    }

    fn empty(&'m self, t: &Type) -> Deep<'m, bool> {
        if t.diagonal_empty() {
            return Stack::ready(true);
        }
        // A member of a recursive group is answered by the group's decider (module `rec`).
        if let Some(b) = t.judged() {
            return Stack::ready(b);
        }
        if let Some(b) = self.group_verdict(t) {
            return Stack::ready(b);
        }
        // A scalar in the type is a checked value, read off before the type is compared with
        // those met.
        let p = t.p();
        let lits = [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings];
        if p.bools != 0 || lits.iter().any(|l| l.cofinite || !l.values.is_empty()) {
            return Stack::ready(false);
        }
        // A type whose values' heights are bounded by an empty range has none
        // ([`height_bounds`]); like the diagonal, a fact of the type alone. Asked only
        // of a type with an atom of a non-empty payload, as a list is: skipping it is sound, as
        // it only ever shows a type empty.
        // Complexity tradeoff: asked of every type, it cost each new type of a search the
        // bounds of the type from its children's, about 73,000 instructions a level of a
        // verdict on tuples of bare atoms n deep and 94,000 of a difference (bounds 286,000 and
        // 245,000 in `deep_ops::subtype_fits_why_and_diff_cost_a_bounded_number_of_instructions_a_level`,
        // over by 15% and 30%), where a tuple's heights are those its components give and no
        // range comes out empty that the search would not refute a level down. The meets it is
        // for, of lists of different lengths (`R_a & R_b`, SUB-fork-place-512), are atom types
        // with a payload, and a tuple or a part that holds one reaches it a level down, where it
        // is asked. Given up: a tuple type whose components' heights clash is refuted by the
        // search at its components, not here.
        if !t.p().atoms.payloads().is_empty() && height_bounds(t).is_none() {
            return Stack::ready(true);
        }
        let i = match self.s().met(t) {
            ControlFlow::Break(b) => return Stack::ready(b),
            ControlFlow::Continue(i) => i,
        };
        self.stack.call(move || async move {
            let b = self.decided(i).await;
            let mut guard = self.s();
            let s = &mut *guard;
            s.deciding.remove(&i);
            if let Some(c) = s.current {
                s.add_reader(i, c);
            }
            b
        })
    }

    /// The current type and a new epoch, which tags the reads and blame added from here on, so
    /// [`Searching::take_fork`] can find them.
    // Complexity tradeoff (COMPLEXITY.md K102): the naive rollback copies the reads and blame
    // at each snapshot, O(R + B) a snapshot; an epoch costs O(1), and since the epochs in each
    // list rise, a rollback finds its start by binary search, O(log R + log B), and moves only
    // what was added after it. Given up: an epoch number per read and per blame entry.
    fn fork_snapshot(&self) -> Option<(Option<usize>, usize)> {
        let mut guard = self.s();
        let s = &mut *guard;
        if s.open_forks {
            return None;
        }
        s.blame.as_ref()?;
        s.epoch += 1;
        Some((s.current, s.epoch))
    }

    fn take_fork(
        &self,
        snap: Option<(Option<usize>, usize)>,
        sub: Option<&Type>,
    ) -> Option<ForkSave> {
        let (c, ep) = snap?;
        let mut guard = self.s();
        let s = &mut *guard;
        let on_fork = s.blame.as_ref().is_some_and(|b| {
            let start = b.partition_point(|&(_, _, e)| e < ep);
            b[start..]
                .iter()
                .any(|&(x, r, _)| r == Refusal::Fork && Some(x) == c)
        }) || {
            let read: &[(usize, usize)] = c.map_or(&[], |c| {
                let start = s.reads[c].partition_point(|&(_, e)| e < ep);
                &s.reads[c][start..]
            });
            let sub = sub.and_then(|t| s.ids.get(t)).copied();
            let from: Vec<usize> = (read.iter())
                .filter_map(|&(packed, _)| {
                    let (u, empty_dep) = unpack_read(packed);
                    empty_dep.then_some(u)
                })
                .chain(sub)
                .collect();
            !from.is_empty() && s.rests_on_fork(from)
        };
        if !on_fork {
            return None;
        }
        let saved_reads = c.map_or_else(Vec::new, |c| s.drop_reads_since(c, ep));
        let saved_blame = s.take_blame_since(c, ep);
        Some((saved_reads, saved_blame))
    }

    /// Drops reads and blame recorded for the type being decided since `snap`, when a speculative
    /// subtype or split check does not apply and leaves the part unchanged.
    fn discard_since(&self, snap: Option<(Option<usize>, usize)>) {
        let Some((c, ep)) = snap else {
            return;
        };
        let mut guard = self.s();
        let s = &mut *guard;
        if let Some(c) = c {
            s.drop_reads_since(c, ep);
        }
        s.take_blame_since(c, ep);
    }

    /// Takes out the reads and blame recorded for the type being decided since `snap`, whatever
    /// they rest on; `None` when there are none.
    fn take_all_since(&self, snap: Option<(Option<usize>, usize)>) -> Option<ForkSave> {
        let (c, ep) = snap?;
        let mut guard = self.s();
        let s = &mut *guard;
        let saved_reads = c.map_or_else(Vec::new, |c| s.drop_reads_since(c, ep));
        let saved_blame = s.take_blame_since(c, ep);
        if saved_reads.is_empty() && saved_blame.is_empty() {
            None
        } else {
            Some((saved_reads, saved_blame))
        }
    }

    /// In `canonical_blame` mode, rolls back reads and blame added since `snap` when a non-empty
    /// arm of a flat disjunction rests on blame, so an unblamed non-empty arm takes precedence and
    /// blamed arms combine commutatively when no arm is clean.
    fn take_blame_on_false(
        &self,
        snap: Option<(Option<usize>, usize)>,
        sub: Option<&Type>,
    ) -> Option<ForkSave> {
        let (c, ep) = snap?;
        let mut guard = self.s();
        let s = &mut *guard;
        if !s.canonical_blame || s.in_subtype_check {
            return None;
        }
        let read: &[(usize, usize)] = c.map_or(&[], |c| {
            let start = s.reads[c].partition_point(|&(_, e)| e < ep);
            &s.reads[c][start..]
        });
        let refused = |u: usize| !s.answer[u] && !s.witnessed.contains(&u) && s.blamed_node[u];
        // An empty read is blamed when it rests on a fork: the reads are tested in one walk
        // ([`Search::rests_on_fork`]), O(B log B + T + R), not one walk each.
        let blamed = s.blame.as_ref().is_some_and(|b| {
            let start = b.partition_point(|&(_, _, e)| e < ep);
            b[start..].iter().any(|&(x, _, _)| Some(x) == c)
        }) || read.iter().any(|&(packed, _)| {
            let (u, empty_dep) = unpack_read(packed);
            refused(u) || (s.answer[u] && !empty_dep && !s.dead.contains(&u))
        }) || sub.and_then(|t| s.ids.get(t)).is_some_and(|&i| refused(i))
            || s.rests_on_fork(read.iter().filter_map(|&(packed, _)| {
                let (u, empty_dep) = unpack_read(packed);
                empty_dep.then_some(u)
            }));
        if !blamed {
            return None;
        }
        let saved_reads = c.map_or_else(Vec::new, |c| s.drop_reads_since(c, ep));
        let saved_blame = s.take_blame_since(c, ep);
        Some((saved_reads, saved_blame))
    }

    /// Whether `t` is empty, and in a search with `blame` the reads and blame added for the
    /// current type when `t`'s emptiness rests on a fork, rolled back so a fork-free proof can
    /// take precedence and restored ([`Searching::restore_fork`]) only when none does.
    async fn empty_fork(&'m self, t: &Type) -> (bool, Option<ForkSave>) {
        let snap = self.fork_snapshot();
        if !self.empty(t).await {
            return (false, None);
        }
        (true, self.take_fork(snap, Some(t)))
    }

    fn restore_fork(&self, (reads, blame): ForkSave) {
        let mut guard = self.s();
        let s = &mut *guard;
        s.epoch += 1;
        let ep = s.epoch;
        if let Some(c) = s.current {
            for packed in reads {
                let (u, _) = unpack_read(packed);
                s.add_reader(u, c);
                s.push_read(c, packed, ep);
            }
        }
        if let Some(b) = &mut s.blame {
            b.extend(blame.into_iter().map(|(x, r)| (x, r, ep)));
        }
    }

    /// Whether one of `ts` is empty, tried in order up to the first that is without a fork, or
    /// the first that is with one.
    async fn any_empty(&'m self, ts: &[Type]) -> bool {
        if !self.s().canonical_blame {
            let mut first_fork = None;
            for t in ts {
                self.trial(1);
                let tried = self.empty_fork(t).await;
                self.trial(-1);
                match tried {
                    (true, None) => return true,
                    (true, Some(fork)) => {
                        first_fork.get_or_insert(fork);
                    }
                    (false, _) => {}
                }
            }
            if let Some(fork) = first_fork {
                self.restore_fork(fork);
                return true;
            }
            return false;
        }
        let mut first_fork = None;
        let mut non_empty_snaps = Vec::new();
        for t in ts {
            let snap = self.fork_snapshot();
            if !self.empty(t).await {
                if let Some(saved) = self.take_all_since(snap) {
                    non_empty_snaps.push(saved);
                }
                continue;
            }
            match self.take_fork(snap, Some(t)) {
                None => return true,
                Some(fork) => {
                    first_fork.get_or_insert(fork);
                }
            }
        }
        if let Some(fork) = first_fork {
            self.restore_fork(fork);
            return true;
        }
        for saved in non_empty_snaps {
            self.restore_fork(saved);
        }
        false
    }

    async fn parts(&'m self, p: &Parts) -> bool {
        let lits = [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings];
        let canonical = self.s().canonical_blame;
        if p.bools != 0
            || lits.iter().any(|l| l.cofinite || !l.values.is_empty())
            || p.atoms.cofinite()
            || (canonical && (p.structs || p.tuples.rest || p.atoms.bare_names() > 0))
        {
            return false;
        }
        let mut forks = Vec::new();
        let mut blamed_false = Vec::new();
        for a in p.atoms.names().values() {
            if a.bare {
                return false;
            }
            let snap = self.fork_snapshot();
            if !self.empty(&a.payload).await {
                match self.take_blame_on_false(snap, Some(&a.payload)) {
                    None => return false,
                    Some(gu) => blamed_false.push(gu),
                }
                continue;
            }
            if let Some(fork) = self.take_fork(snap, Some(&a.payload)) {
                forks.push(fork);
            }
        }
        if p.structs || p.tuples.rest {
            return false;
        }
        for (len, b) in &p.tuples.lens {
            let normalized = if self.s().tuple_universe {
                let cached = self.s().tuple_universes.get(&b.id()).cloned();
                Some(cached.unwrap_or_else(|| {
                    let p =
                        b.restrict(&|row| row.iter().all(|t| *t == Type::top()).then_some(true));
                    self.s().tuple_universes.insert(b.id(), p.clone());
                    p
                }))
            } else {
                None
            };
            let b = normalized.as_ref().unwrap_or(b);
            let snap = self.fork_snapshot();
            let empty = match b.union_rows() {
                // A union of rows is empty when each row has an empty column, and only then.
                Some(rows) => {
                    let mut all = true;
                    let mut row_forks = Vec::new();
                    let mut row_blamed_false = Vec::new();
                    for a in &rows {
                        let row_snap = self.fork_snapshot();
                        if !self.any_empty(a).await {
                            all = false;
                            match self.take_blame_on_false(row_snap, None) {
                                None => {
                                    row_blamed_false.clear();
                                    break;
                                }
                                Some(gu) => row_blamed_false.push(gu),
                            }
                            continue;
                        }
                        if let Some(fork) = self.take_fork(row_snap, None) {
                            row_forks.push(fork);
                        }
                    }
                    if all {
                        for fork in row_forks {
                            self.restore_fork(fork);
                        }
                    } else {
                        for gu in row_blamed_false {
                            self.restore_fork(gu);
                        }
                    }
                    all
                }
                None => {
                    if self.cofinite_integer_rep(*len, b).is_some() {
                        false
                    } else {
                        let g = self.region(vec![Type::top(); *len], b).await;
                        self.tuples(g, b.clone(), true).await.0
                    }
                }
            };
            if !empty {
                match self.take_blame_on_false(snap, None) {
                    None => return false,
                    Some(gu) => blamed_false.push(gu),
                }
                continue;
            }
            if let Some(fork) = self.take_fork(snap, None) {
                forks.push(fork);
            }
        }
        let snap = self.fork_snapshot();
        let morphisms_empty = match p.morphisms.union_rows() {
            // A union of morphism types is empty when each of them admits nothing.
            Some(mut rows) => {
                // The rows whose value type is a union of morphism rows first: one admitting a
                // morphism decides the union, and such a row needs no split of morphisms.
                rows.sort_by_key(|a| a.value.p().morphisms.union_rows().is_none());
                let mut all = true;
                let mut row_forks = Vec::new();
                let mut row_blamed_false = Vec::new();
                for a in &rows {
                    let row_snap = self.fork_snapshot();
                    if !self.no_morphism(a).await {
                        all = false;
                        match self.take_blame_on_false(row_snap, None) {
                            None => {
                                row_blamed_false.clear();
                                break;
                            }
                            Some(gu) => row_blamed_false.push(gu),
                        }
                        continue;
                    }
                    if let Some(fork) = self.take_fork(row_snap, None) {
                        row_forks.push(fork);
                    }
                }
                if all {
                    for fork in row_forks {
                        self.restore_fork(fork);
                    }
                } else {
                    for gu in row_blamed_false {
                        self.restore_fork(gu);
                    }
                }
                all
            }
            None => {
                self.morphisms(
                    Morphism::new(Type::empty(), Type::top(), Type::top()),
                    p.morphisms.clone(),
                    true,
                )
                .await
            }
        };
        if !morphisms_empty {
            match self.take_blame_on_false(snap, None) {
                None => return false,
                Some(gu) => blamed_false.push(gu),
            }
        }
        if !blamed_false.is_empty() {
            for gu in blamed_false {
                self.restore_fork(gu);
            }
            return false;
        }
        if let Some(fork) = self.take_fork(snap, None) {
            forks.push(fork);
        }
        for fork in forks {
            self.restore_fork(fork);
        }
        true
    }

    /// The region of the part `f` on the box `r`, each distinct type of each component tested
    /// once.
    async fn region(&'m self, r: Vec<Type>, f: &Part<Row>) -> Region {
        let atoms = f.distinct_atoms();
        let n = r.len();
        let mut g = Region {
            priority: 0,
            structural_empty: false,
            cells: (0..n).map(|_| Vec::new()).collect(),
            cell_of: vec![0; atoms.len() * n],
            opens: vec![0; n],
            changed: vec![true; n],
            missed: vec![0; atoms.len()],
            loose: vec![(0, 0); atoms.len()],
            index: DigestMap::default(),
            atoms: Vec::new(),
            log: Vec::new(),
            forked_holds: Vec::new(),
            r,
        };
        for j in 0..n {
            let mut found: DigestMap<&Type, usize> = DigestMap::default();
            for (k, a) in atoms.iter().enumerate() {
                let cells = &mut g.cells[j];
                let c = *found.entry(&a[j]).or_insert_with(|| {
                    cells.push(Cell {
                        ty: a[j].clone(),
                        rows: Vec::new(),
                        open: true,
                    });
                    cells.len() - 1
                });
                cells[c].rows.push(k);
                g.cell_of[k * n + j] = c;
                g.opens[j] += 1;
                g.loose[k].0 += 1;
                g.loose[k].1 += j;
            }
        }
        for (k, a) in atoms.iter().enumerate() {
            g.index.insert(a.clone(), k);
        }
        g.atoms = atoms;
        if n != 0 {
            // Complexity tradeoff: testing a varying column first unfolds n common
            // constraints in n contexts, O(n^2) on the morphism result family. Cache
            // each node's outer carriers and choose one shared column in O(incidences).
            // Nine Boolean evaluations with row lookups cost O((part nodes + incidences) log n);
            // its mandatory fields are met pairwise through the cut memo, O(n log n).
            // Mandatory rows are a sufficient syntactic subset (forced_factors), not
            // a full analysis of common atoms hidden under union arms. Only a false
            // formula proves emptiness; otherwise
            // the original tests run, with the most restrictive shared column first.
            // Test: cycle_dup::shared_morphism_constraints_are_checked_in_the_size_of_the_union.
            let taken = f.forced_factors();
            let mut required = vec![false; g.atoms.len()];
            for a in &taken {
                required[g.index[a]] = true;
            }
            let kinds: Vec<Vec<u16>> = g
                .cells
                .iter()
                .map(|cells| {
                    cells
                        .iter()
                        .map(|cell| self.outer_kinds(&cell.ty))
                        .collect()
                })
                .collect();
            let mut best = u32::MAX;
            for j in 0..n {
                let mut union = 0u16;
                for (k, _) in g.atoms.iter().enumerate() {
                    if !required[k] {
                        union |= kinds[j][g.cell(k, j)];
                    }
                }
                let score = union.count_ones();
                if score < best {
                    best = score;
                    g.priority = j;
                }
            }
            let j = g.priority;
            // Complexity tradeoff (PERF-deep-ops-slow): a kind of the meet of the box's column
            // with the taken cells is a kind of each of them, read from the cache with nothing
            // built, so the formula is tried first on the kinds all of them have. Where only
            // the tuple kind fails it, whether the meet holds a tuple is read from the lengths
            // ([`Tuples::may_meet`]); the meet is built only where another kind fails. Naive
            // version (GSX-unsolved): the meet built at every region, about 37k instructions a
            // level of each search through tuples nested 20,000 deep (verdict 251k a level,
            // 189k before the check). The lengths miss a meet empty only by form, one part the
            // complement of another; such a region is then tested cell by cell, as before the
            // check, where that meet is built and found empty, so no answer changes.
            let operands = || std::iter::once(&g.r[j]).chain(taken.iter().map(|a| &a[j]));
            let within = operands().fold(u16::MAX, |b, t| b & self.outer_kinds(t));
            let failing = (0..9).map(|bit| 1u16 << bit).fold(0, |failing, bit| {
                let fails = within & bit != 0
                    && f.eval3(&|a| {
                        let k = g.index[a];
                        if required[k] {
                            Some(true)
                        } else if kinds[j][g.cell(k, j)] & bit == 0 {
                            Some(false)
                        } else {
                            None
                        }
                    }) != Some(false);
                failing | if fails { bit } else { 0 }
            });
            const TUPLE: u16 = 1 << 6;
            g.structural_empty = match failing {
                0 => true,
                TUPLE => {
                    let ps: Vec<_> = operands().map(Type::p).collect();
                    !Tuples::may_meet(&ps.iter().map(|p| &p.tuples).collect::<Vec<_>>())
                }
                _ => {
                    let projected = Type::pairwise(operands().cloned(), Type::top(), |a, b| {
                        self.cut(&a, &b, Cut::Meet)
                    });
                    self.outer_kinds(&projected) & failing == 0
                }
            };
        }
        if !g.structural_empty {
            self.retest(&mut g).await;
        }
        g.log.clear();
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
    /// given up is the hits on equal operands built apart. COMPLEXITY.md K51. Naive version:
    /// no memo, or a scan of the search's types at each call, which failed `nested_tuples_scale`
    /// at 34.0 times from depth 400 to 3200 (limit 24); used: one build per pair of operand
    /// nodes, a hash lookup by local node number per call.
    async fn settles(&'m self, x: &Type, y: &Type, both: bool) -> bool {
        if let Some(b) = self.scalar_cell(x, y, both) {
            return b;
        }
        let t = self.cut(x, y, if both { Cut::Meet } else { Cut::Minus });
        self.empty(&t).await
    }

    /// Exact scalar tests shared by cells and by the general settles query.
    // Complexity tradeoff: checking one pair in c columns rereads its l literal
    // entries O(c*l log l). Cache the exact result, O(l log l) once and O(1)
    // expected per repeated query, with O(number of scalar pairs) stored bits.
    // Node numbers are never reused. Non-scalar misses only inspect carrier
    // heads and are recomputed, so the memo retains no operand graph.
    // Equal nodes built apart miss the memo; no answer is given up. Test:
    // setop::shared_integer_columns_scale_with_their_written_dag; the version
    // without this memo fails the same check, even with scalar points memoized.
    fn scalar_cell(&self, x: &Type, y: &Type, both: bool) -> Option<bool> {
        let key = (x.node_id(), y.node_id(), both);
        if let Some(&value) = self.s().scalar_cells.get(&key) {
            return Some(value);
        }
        let value = x.scalar_cell(y, both);
        if let Some(value) = value {
            self.s().scalar_cells.insert(key, value);
        }
        value
    }

    /// `x op y`, built once per pair of nodes and kept in `cuts`, as for [`Searching::settles`]:
    /// the search reads the same morphism types again and again, and the meets and differences
    /// of their fields were built at each read, each a node of its own that `empty` then looked
    /// up by its contents (EMPTY-morphism-next). The tradeoff of keying by node is that of
    /// `settles`.
    fn cut(&self, x: &Type, y: &Type, op: Cut) -> Type {
        let key = (x.node_id(), y.node_id(), op);
        (self.s().cuts.entry(key))
            .or_insert_with(|| (x.clone(), y.clone(), op.of(x, y)))
            .2
            .clone()
    }

    /// The morphisms both `a` and `b` admit, each field built once per pair of nodes.
    fn meet(&self, a: &Morphism, b: &Morphism) -> Morphism {
        Morphism::new(
            self.cut(&a.guarantee, &b.guarantee, Cut::Join),
            self.cut(&a.permission, &b.permission, Cut::Meet),
            self.cut(&a.value, &b.value, Cut::Meet),
        )
    }

    /// A necessary outer value kind, cached for every exposed node of this search. Payloads
    /// and function fields are not followed: a bit records only that their carrier is present.
    fn outer_kinds(&self, t: &Type) -> u16 {
        if let Some(bits) = self.s().outer_kinds.get(&t.node_id()).copied() {
            return bits;
        }
        let p = t.p();
        let mut bits = u16::from(p.bools != 0);
        for (j, l) in [&p.ints, &p.rats, &p.floats, &p.strings].iter().enumerate() {
            bits |= u16::from(l.cofinite || !l.values.is_empty()) << (j + 1);
        }
        bits |= u16::from(p.atoms.cofinite() || !p.atoms.names().is_empty()) << 5;
        bits |= u16::from(p.tuples.rest || !p.tuples.lens.is_empty()) << 6;
        bits |= u16::from(p.structs) << 7;
        bits |= u16::from(p.morphisms.is_leaf() != Some(false)) << 8;
        bits |= u16::from(p.f32s.cofinite || !p.f32s.values.is_empty()) << 9;
        self.s().outer_kinds.insert(t.node_id(), bits);
        bits
    }

    /// Tests each changed component of the box against its open cells that have a tuple type
    /// not yet known to miss the box, and closes those it settles. A tuple type that misses a
    /// component is out of the part, so whether it holds the others is not tested: every
    /// changed component is tested for cells that miss it before any is tested for cells that
    /// hold it, and a cell only such tuple types have is not tested. Tuple types the part no
    /// longer has are not looked up: that costs the size of the part at each call, more than
    /// the tests it saves.
    async fn retest(&'m self, g: &mut Region) {
        let mut changed: Vec<usize> = (0..g.r.len()).filter(|&j| g.changed[j]).collect();
        if let Some(at) = changed.iter().position(|&j| j == g.priority) {
            changed[..=at].rotate_right(1);
        }
        if changed.is_empty() {
            return;
        }
        for &j in &changed {
            g.changed[j] = false;
            g.log.push(Change::Tested(j));
        }
        for missed in [true, false] {
            let mut forked = Vec::new();
            for &j in &changed {
                for c in 0..g.cells[j].len() {
                    let cell = &g.cells[j][c];
                    if !cell.open || !cell.rows.iter().any(|&k| g.missed[k] == 0) {
                        continue;
                    }
                    if missed {
                        if let Some(b) = self.scalar_cell(&g.r[j], &cell.ty, true) {
                            if b {
                                g.close(j, c, true);
                            }
                            continue;
                        }
                        let t = self.cut(&g.r[j], &cell.ty, Cut::Meet);
                        match self.empty_fork(&t).await {
                            (true, None) => g.close(j, c, true),
                            (true, Some(fork)) => forked.push((j, c, fork)),
                            (false, _) => {}
                        }
                    } else {
                        if let Some(b) = self.scalar_cell(&g.r[j], &cell.ty, false) {
                            if b {
                                g.close(j, c, false);
                            }
                            continue;
                        }
                        let sub_snap = self.fork_snapshot();
                        let t = self.cut(&g.r[j], &cell.ty, Cut::Minus);
                        let prev_sub = std::mem::replace(&mut self.s().in_subtype_check, true);
                        let res = self.empty_fork(&t).await;
                        self.s().in_subtype_check = prev_sub;
                        match res {
                            (true, None) => g.close(j, c, false),
                            (true, Some(fork)) => g.forked_holds.push((j, c, fork)),
                            (false, _) => self.discard_since(sub_snap),
                        }
                    }
                }
            }
            for (j, c, fork) in forked {
                if g.cells[j][c].rows.iter().any(|&k| g.missed[k] == 0) {
                    self.restore_fork(fork);
                }
                g.close(j, c, true);
            }
        }
    }

    /// Counts a trial of a component in [`Searching::any_empty`] begun (+1) or ended (-1).
    fn trial(&self, step: isize) {
        if let Some(n) = &mut self.s().trials {
            *n = n.wrapping_add_signed(step);
        }
    }

    /// Notes a fork met in the decision of a verdict: against the type being decided in a search
    /// with several roots, else as the refusal that ends the search.
    fn refuse_fork(&self) {
        let mut guard = self.s();
        let s = &mut *guard;
        let ep = s.epoch;
        match (&mut s.blame, s.current) {
            (Some(blame), Some(c)) if s.trials.is_none_or(|n| n > 0) => {
                blame.push((c, Refusal::Fork, ep))
            }
            // Complexity tradeoff: a fork met while no type is being decided cannot be put on
            // the roots that read it, so it ends the search and refuses every root the decider
            // left open, as it refuses the one root of a search of its own. Trigger: `current`
            // is none at a fork. COMPLEXITY.md K61. Naive version: a search of its own per open
            // member, n searches of a group of n, O(n²); used: one search with every open member
            // as a root, so one fork outside any type being decided refuses them all.
            _ => s.refused = Some(Refusal::Fork),
        }
    }

    /// Narrows the box and the part `f` to what `f` forces on it: a tuple type in every value
    /// of `f` meets the box, and a tuple type in none is taken out of the box when it holds the
    /// box in every component but one. True when `f` is proved empty on the box. Two tuple types
    /// it would take out of one component with different recursive types there, each on a
    /// cycle of its group, are a fork: unless the component less its cuts on no cycle is one of
    /// those recursive types, the decision of a verdict refuses there, and the search of a value
    /// keeps that component.
    async fn narrow_tuples(&'m self, g: &mut Region, f: &mut Part<Row>) -> bool {
        if g.structural_empty {
            return true;
        }
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
                        // Complexity tradeoff: c scalar columns sharing l literals
                        // rebuild their meet in O(c*l log l) work. Reuse the
                        // cut memo: one meet per pair and one lookup per incidence,
                        // with no precision change. The test
                        // shared_integer_columns_scale_with_their_written_dag
                        // passes here and fails without the memo. Non-scalar meets
                        // keep their existing path, without retaining speculative
                        // recursive operand graphs in an additional cache.
                        let next = if self.scalar_cell(&g.r[j], &a[j], true).is_some() {
                            self.cut(&g.r[j], &a[j], Cut::Meet)
                        } else {
                            &g.r[j] & &a[j]
                        };
                        g.shrink(j, next);
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
            // Complexity tradeoff: two tuple types taken out of one component with different
            // recursive types there, each on a cycle of its group (`Type::on_cycle`; one on no
            // cycle unfolds to others in a bounded number of steps and is decided as before),
            // are a fork, as two open tuple types that differ in a recursive component are
            // (`tuples_on`): the decision of a verdict refuses the part, and the search of a
            // value keeps the component whole there, counting it inhabited.
            // Why: the component less both is a new type, whose decision takes out what each
            // leaves of its tail, and so on, one type for each set of tails met: the subset
            // construction, exponential in the recursive types (the lists of int against lists
            // with a 1 at each place from the end up to `n`, and beyond it, cost 13.2G
            // instructions at `n` 8; whether such a union holds every list is NFA universality,
            // PSPACE-complete). Hardness of what is refused: an automaton with states `q`,
            // letters `1..k` and moves `q -a-> q'` becomes, in linear size, the group
            // `X_q = cons(a, X_q') | ..`, with `| nil` where `q` accepts; it accepts every word
            // exactly when `list(1..k)` less `X_q0` is empty. This search answers in polynomial
            // time on every difference and is exact on every one it does not refuse, so, unless
            // P = PSPACE, the refused ones are not all decidable in polynomial time. The end
            // family is the standard case: its smallest deterministic form, read from the
            // front, has `2^n` states. Easy differences refused with it: the end family itself
            // (Empty; read from the end it still forks, between the lists with no 1 and those
            // with a 1 past place `n`), the same family less one place (Inhabited: a value is
            // `[1, 0, ..]`; reversed by hand the search finds it, but the kernel has no reversal
            // of list types, follow-up REFUSAL-reverse-words), and periodic lists mixing periods
            // (unary universality, coNP-complete: the shortest value can be as long as the
            // product of the periods). Trigger: two tuple types this pass takes out of one
            // component with different recursive types on a cycle there, in the decision of a
            // verdict or the search of a value after it. Tests:
            // `l01_23_groups_and_refusals::refusals::bench::a_union_of_lists_by_the_place_of_a_one_is_refused_in_its_size`
            // and `each_refusal_names_its_cause` (`nfa`). COMPLEXITY.md K35. A complete solution
            // needs the subset construction over the forked tuple types, exponential in them.
            let (refuse, open) = {
                let s = self.s();
                (s.refuse_forks && !s.seeding, s.open_forks)
            };
            let mut forked = BTreeSet::new();
            if refuse || open {
                let mut first: BTreeMap<usize, &Type> = BTreeMap::new();
                for a in &refused {
                    let k = g.index[a];
                    let (loose, at) = g.loose[k];
                    if g.missed[k] == 0 && loose == 1 && a[at].on_cycle() {
                        let t = *first.entry(at).or_insert(&a[at]);
                        if *t != a[at] {
                            forked.insert(at);
                        }
                    }
                }
            }
            // Complexity tradeoff (GROUP-order-classes-outside-cpoly, COMPLEXITY.md K35b): before
            // a fork is met, each forked component less its cuts on no cycle, built as a type and
            // not decided, is compared with the recursive types cut there: when it is one of them
            // or the empty type, the cuts there hold the component, so `f` is empty on the box.
            // Whether such a fork was refused came with the order of the components (finding
            // F5: `((#a | #b), (L12 | #c))` less five pairs: a split on the first component left
            // L1, L12 and `#c` to take out of the second, refused, though `(L12 | #c) - #c` is
            // L12; a split on the second first decided Empty). Naive: refuse at once, as before.
            // Tried and dropped, each order `n^2` on the lists by the place of a 1 from the end
            // (`G{i}` walks `i` levels): deciding the component less each recursive type alone,
            // 13.35 times from n 64 to 512 against 8.09; taking the cuts on no cycle out first and
            // testing the cells again, which tests every recursive type against the new
            // component, past the 25 s limit. Used: one difference per cut on no cycle at the
            // component, as its narrowing would build, and one lookup among the recursive types
            // and their kept unrollings by content digest (`Type`'s `Ord`), O(r log r) for `r`
            // cuts; no type is decided, so the search goes no deeper than before. Sound: each cut
            // counted holds the box in every other component (`missed` 0, `loose` 1), so cuts
            // whose union holds this component leave `f` no value on the box. Not caught: a
            // component the cuts hold whose rest is neither one recursive type nor members of
            // their union, which stays refused (see the union check below).
            let mut held = false;
            for &at in &forked {
                let (mut rest, mut cyc) = (g.r[at].clone(), BTreeSet::new());
                for a in &refused {
                    let k = g.index[a];
                    if g.missed[k] == 0 && g.loose[k] == (1, at) {
                        if a[at].on_cycle() {
                            // The box's component holds a recursive type unrolled one level,
                            // so the rest is compared with each cut and with its unrolling,
                            // kept on the node (`Type::p`): O(1) per cut once made.
                            if let PartsRef::Unfolded(u) = a[at].p() {
                                cyc.insert(u);
                            }
                            cyc.insert(a[at].clone());
                        } else {
                            rest = &rest - &a[at];
                        }
                    }
                }
                held |= rest == Type::empty() || cyc.contains(&rest) || {
                    // GROUP-order-fork-cuts-together: the rest may be held by several recursive
                    // cuts together and by no one of them, as `(#a, E | O)` less `(#a, E)` and
                    // `(#a, O)`. Their union is built once, in balanced halves (each union merges
                    // two sorted member lists, so `r` cuts cost O(r log^2 r) against O(r^2 log r)
                    // for a left fold), and the rest counts as held when adding it leaves the
                    // union unchanged: every member of the rest is a member of the union, by the
                    // union's canonical form, so no type is decided. What this misses needs
                    // the subset construction: `(#a, list(int))` less the same two pairs is
                    // Empty, but `list(int)` within `E | O` is the universality of the union of
                    // two automata (NFA universality, PSPACE-complete; see the fork comment
                    // above), so it stays refused. Test:
                    // `refusals::a_fork_emptied_by_two_list_types_together_is_decided_in_both_orders`.
                    let mut layer: Vec<Type> = cyc.iter().cloned().collect();
                    while layer.len() > 1 {
                        layer = layer
                            .chunks(2)
                            .map(|p| {
                                if p.len() == 2 {
                                    &p[0] | &p[1]
                                } else {
                                    p[0].clone()
                                }
                            })
                            .collect();
                    }
                    layer.pop().is_some_and(|u| (&rest | &u) == u)
                };
            }
            if held {
                return true;
            }
            if !forked.is_empty() {
                if refuse {
                    self.refuse_fork();
                    return true;
                }
                let mut s = self.s();
                s.give_up(Refusal::Fork);
                s.kept_forks += 1;
            }
            for a in &refused {
                let k = g.index[a];
                let (loose, at) = g.loose[k];
                if g.missed[k] == 0 && loose == 1 && !forked.contains(&at) {
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
            if self.s().open_forks {
                let open: Vec<usize> = f.distinct_atoms().iter().map(|a| g.index[a]).collect();
                if (0..g.r.len()).any(|j| g.forks(&open, j)) {
                    // Complexity tradeoff: the search of a value after a refused decision counts
                    // a part whose open tuple types fork as inhabited, before narrowing, and so
                    // builds no value in it from this box. Why: narrowing takes the forked tuple
                    // types out of a component, and deciding what is left of it is the subset
                    // construction (the tradeoff in `narrow_tuples`); the decision of a value's
                    // check by its own walk stays exact. Trigger: `open_forks` and a component on
                    // which the open tuple types fork. Tests:
                    // `l01_23_groups_and_refusals::refusals::bench::a_union_of_lists_by_the_place_of_a_one_is_refused_in_its_size`
                    // and `a_value_found_by_refining_a_forked_part_is_kept`. COMPLEXITY.md K35.
                    // A complete solution needs the subset construction over the forked tuple
                    // types, exponential in them; used: no value sought in that part, so the
                    // search stays polynomial in the types written.
                    self.s().give_up(Refusal::Fork);
                    return false;
                }
            }
            if self.narrow_tuples(g, &mut f).await {
                return true;
            }
            if f.is_leaf().is_some() {
                return false;
            }
            let top = Type::top().node_addr();
            if self.s().blame.is_some()
                && g.r.iter().all(|t| t.node_addr() == top)
                && let Some(rows) = f.union_rows()
            {
                let mut all = true;
                let mut forks = Vec::new();
                let mut blamed_false = Vec::new();
                for a in &rows {
                    let snap = self.fork_snapshot();
                    if !self.any_empty(a).await {
                        all = false;
                        match self.take_blame_on_false(snap, None) {
                            None => {
                                blamed_false.clear();
                                break;
                            }
                            Some(gu) => blamed_false.push(gu),
                        }
                        continue;
                    }
                    if let Some(fork) = self.take_fork(snap, None) {
                        forks.push(fork);
                    }
                }
                if all {
                    for fork in forks {
                        self.restore_fork(fork);
                    }
                    return true;
                }
                for gu in blamed_false {
                    self.restore_fork(gu);
                }
                let open: Vec<usize> = f.distinct_atoms().iter().map(|a| g.index[a]).collect();
                let forking = {
                    let s = self.s();
                    s.refuse_forks && !s.seeding
                };
                if forking && (0..g.r.len()).any(|j| g.forks(&open, j)) {
                    self.s().give_up(Refusal::Fork);
                }
                return false;
            }
            let open: Vec<usize> = f.distinct_atoms().iter().map(|a| g.index[a]).collect();
            if self.s().blame.is_some() && empty_by_classes(g, &f, &open) {
                return true;
            }
            if let Some((j, classes, by_keys)) = classes(g, &open, true) {
                if !by_keys {
                    let mut each = Each::Decide { may_cover };
                    return self.split_classes(g, &f, j, &classes, &mut each).await;
                }
                // The regions of flat keys ([`key_pieces`]) are the pieces of component `j` cut
                // by the open cells, and this is DESIGN.md L1.23's step "each piece on which
                // narrowing alone proves the part empty is taken out of the box", for cells
                // that may cross: when narrowing alone proves the part empty on every piece and
                // on the rest of the component, the box is empty. Otherwise nothing read here
                // is kept and the steps below run as before, so the check decides the same
                // parts it did, and refuses those that need a split of the box in two
                // components at once.
                let snap = self.fork_snapshot();
                let mut failed = false;
                let mut each = Each::Narrow {
                    failed: &mut failed,
                };
                if self.split_classes(g, &f, j, &classes, &mut each).await && !failed {
                    return true;
                }
                self.discard_since(snap);
            }
            let forking = {
                let s = self.s();
                s.refuse_forks && !s.seeding
            };
            if forking && (0..g.r.len()).any(|j| g.forks(&open, j)) {
                // Complexity tradeoff: `verdict` refuses a part in which two open tuple types
                // differ in a recursive component on one box, instead of following both. Why:
                // following both is the subset construction, exponential in the recursive types
                // (hard by the reduction at the fork in `narrow_tuples`); `is_empty` stops here
                // too and counts the type as inhabited. A union of pure cycles less one other,
                // as `(P(6,4) | P(12,4))` less `P(3,1)` of lengths modulo periods, never reaches
                // this refusal: `cycle_meet` reads it and `union_classes` decides it in
                // `O(n log n)`. A split into the open tuple types below, run before this
                // refusal, is order `n` pieces by a part of `n` nodes on
                // `refusals::a_difference_of_forked_unions_is_refused_in_its_size` (62 times the
                // bytes at 8 times `n`; REFUSAL-nfa-refuse, not kept). Trigger: a
                // component on which the open tuple types fork, outside seeding. Tests:
                // `l01_23_groups_and_refusals::refusals::each_refusal_names_its_cause` (`fork_empty`) and
                // `a_value_is_sought_before_a_refusal` (`fork`). COMPLEXITY.md K26 and the Kept
                // row "emptiness and subtyping of tuple and morphism parts". A complete solution
                // needs the subset construction over the forked rows (a tree automaton
                // determinized on demand), exponential in the rows of the fork. A search with
                // several roots refuses only those that read the type being decided
                // (`Search::causes`). Used: the refusal, so the search stays polynomial in the
                // types written (module comment).
                //
                // Complexity tradeoff (COMPLEXITY.md K134, REFUSAL-front-post-r11-forks): when
                // the part is a plain union of tuple types (`Part::union_rows`: no tuple type
                // taken out), one candidate value per tuple type of it before the refusal: the
                // row met with that tuple type, a value of it kept when it is in the part
                // (`row_rep`, an exact membership test). A value found proves the part
                // inhabited, so the fork needs no following and the answer is exact. Naive
                // version: the refusal alone, which refused 4 of the 22 U6 cases that kernel
                // 19bc4e25 answered. Cost: one value search per tuple type of the union at each
                // fork, the work the seeding does once per tuple part (`Searching::find_rep`).
                // Not done: the same candidates for a part that takes tuple types out; each
                // candidate's membership test then reads the n tuple types taken out, n
                // candidates by n, and the forked-differences benches
                // (`refusals::bench::a_pair_type_met_with_forked_differences`,
                // `a_union_of_forked_differences`, `a_difference_of_forked_unions`) timed out
                // at their limits (63 to 108 s). Given up: a part whose values lie in no single tuple type
                // of it, or that takes tuple types out, still needs the subset construction and
                // is refused (REFUSAL-front-u6-subset). Tests:
                // `sweep_agreement::the_u6_fork_cases_are_answered_or_refused_soundly`.
                for a in f.union_rows().unwrap_or_default() {
                    let row: Vec<Type> = g.r.iter().zip(a.iter()).map(|(x, y)| x & y).collect();
                    if self.row_rep(&row, &f).await.is_some() {
                        return false;
                    }
                }
                self.refuse_fork();
                return true;
            }
            if let Some(found) = self.two_sat(g, &f).await {
                return found.is_none();
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
                let open_cells = g.open_cells(j, &open);
                let split_snap = self.fork_snapshot();
                let mut pieces: BTreeMap<Type, Vec<usize>> = BTreeMap::new();
                let mut union = Type::empty();
                let mut ok = true;
                for &c in &open_cells {
                    let piece = &g.cells[j][c].ty & &g.r[j];
                    if let Some(cs) = pieces.get_mut(&piece) {
                        cs.push(c);
                        continue;
                    }
                    if self.empty_fork(&(&piece & &union)).await != (true, None) {
                        ok = false;
                        break;
                    }
                    union = &union | &piece;
                    pieces.insert(piece, vec![c]);
                }
                if !ok {
                    self.discard_since(split_snap);
                    continue;
                }
                let mut all: Vec<(Type, Vec<usize>)> = pieces.into_iter().collect();
                let rest = &g.r[j] - &union;
                let rest_snap = self.fork_snapshot();
                if self.empty_fork(&rest).await != (true, None) {
                    self.discard_since(rest_snap);
                    all.push((rest, Vec::new()));
                }
                let mut forks = Vec::new();
                for (c, held) in all {
                    let mark = g.log.len();
                    let holds_mark = g.forked_holds.len();
                    g.shrink(j, c);
                    for &cell in &open_cells {
                        g.close(j, cell, !held.contains(&cell));
                    }
                    let snap = self.fork_snapshot();
                    let (b, back) = self.tuples(std::mem::take(g), f.clone(), may_cover).await;
                    *g = back;
                    g.forked_holds.truncate(holds_mark);
                    g.restore(mark);
                    if !b {
                        return false;
                    }
                    if let Some(fork) = self.take_fork(snap, None) {
                        forks.push(fork);
                    }
                }
                for fork in forks {
                    self.restore_fork(fork);
                }
                return true;
            }
            // Complexity tradeoff: the one pass is tried only where the split below may follow,
            // not in that split's pieces, so a piece the pass would decide is left to the search
            // as before the pass. Why: each of the `k` pieces holds the whole part, and a pass
            // that gives no answer has still walked it, `k` walks in all (the choice chain
            // against a swapped one in `l01_23_subtyping::x13` grew 237 times in bytes at 8
            // times `d`, above its order `d²`). Trigger: `may_cover` false. COMPLEXITY.md K71.
            // Used: one pass per part, each node read once, linear in the part (K71: the one
            // pass decided these meets in one walk).
            let mut unread = None;
            if may_cover {
                match self.one_pass(g, &f, &open).await {
                    Some(Ok(empty)) => return empty,
                    Some(Err(j)) => unread = Some(j),
                    None => {}
                }
            }
            if may_cover
                && f.eval3(&|_| Some(false)) == Some(false)
                && let Some(j) = unread
            {
                // Complexity tradeoff: a part of one choice per component that the one pass
                // leaves undecided, at an `&` or `|` whose operands share component `j` and are
                // not both decision lists or exclusive ors under `!` (such as an `&` of three
                // lists on two components), counts as inhabited for `is_empty`, and `verdict`
                // answers `Refused(SharedCells(j))` unless `Searching::refine` finds a value
                // first. Why: such parts encode Orthogonal Vectors with two components
                // (component 0 picks one of `n` cells `u`, component 1 one of `n` cells `v`, and
                // the part is the `and` over the dimensions `d` of `!(U_d & V_d)`, `U_d` the union
                // of the cells `u` with `u[d] = 1`), so no exact method takes `O(n^(2-e))` time
                // unless the Orthogonal Vectors hypothesis fails; the split into the open tuple
                // types below decided them in order `c²` (author's answer A46: refuse). Trigger:
                // `Choices::pair` meets an operand that is no list or exclusive or. Tests:
                // `l01_23_subtyping::one_pass::an_orthogonal_vectors_meet_is_refused_naming_its_component`
                // and `random_parts_out_of_the_class_are_decided_or_refused`. COMPLEXITY.md K71. A
                // complete solution needs the split, order `c²` and worse with more operands.
                // Used: the one pass, each node once, and the refusal; the K71 scaling tests
                // hold the class it decides to n log n.
                self.s().give_up(Refusal::SharedCells(j));
                return false;
            }
            // Complexity tradeoff: a part false when every open tuple type is false, that the
            // one pass above does not read (a tuple type open on two components, or two open
            // cells of one component that may share a value), is split into its open tuple
            // types, each piece deciding the whole part again: `k` pieces of a part of `n`
            // nodes. Why: such parts are covers of the box by tuple types, coNP-hard in
            // general, and the split keeps the search polynomial. Trigger: `may_cover`, and
            // `one_pass` finds the part not of one choice per component. Tests: the split's
            // cases in `l01_23_subtyping::x13` and `l01_23_subtyping::scaling`. COMPLEXITY.md
            // K71 and the Kept row "emptiness and subtyping of tuple and morphism parts". A
            // complete solution needs a split of the box in every component.
            if may_cover && f.eval3(&|_| Some(false)) == Some(false) {
                // A union of parts that share no tuple type is empty when each part is, each
                // decided on the box with only its own tuple types: `n` parts of `c` tuple types
                // each cost order `n c`, not the `n c` pieces by the whole part of the split
                // below (`l01_23_groups_and_refusals::refusals::a_union_of_pairs_less_pairs_holding_them_is_empty_in_its_size`,
                // COMPLEXITY.md K80).
                if let Some(parts) = f.disjoint_disjuncts() {
                    let mut all_empty = true;
                    let mut forks = Vec::new();
                    let mut blamed_false = Vec::new();
                    for d in parts {
                        let snap = self.fork_snapshot();
                        if !self.piece(g.r.clone(), d, true).await {
                            all_empty = false;
                            match self.take_blame_on_false(snap, None) {
                                None => return false,
                                Some(gu) => blamed_false.push(gu),
                            }
                            continue;
                        }
                        if let Some(fork) = self.take_fork(snap, None) {
                            forks.push(fork);
                        }
                    }
                    if !all_empty {
                        for gu in blamed_false {
                            self.restore_fork(gu);
                        }
                        return false;
                    }
                    for fork in forks {
                        self.restore_fork(fork);
                    }
                    return true;
                }
                // DESIGN.md L1.23 takes out each piece on which narrowing alone proves the part
                // empty before it splits the box into the open tuple types, and narrows the box
                // left again (TEST-may-cover-piece-removal): the split's piece of a tuple type
                // that holds the box once a piece is out is that whole box, which its branch
                // cannot split again, so a split first refuses boxes the taking out settles
                // (`l01_23_groups_and_refusals::nested_cover::a_piece_taken_out_before_the_split_leaves_a_box_the_split_settles`).
                //
                // Complexity tradeoff: the pieces are taken out over several passes of this loop,
                // each narrowing the box again, and a pass may try a cell that missed on an earlier
                // pass again, where a pass that took out every piece it could would try each cell
                // once. Why: each piece is narrowed on the box as it stands (DESIGN.md L1.23, the
                // proof at `nested_cover`). Bound (PERF-take-out-piece-chain): the loop goes back
                // to its top only here and below at `take_out_piece`, and at most `1 + Σ_j
                // |cells[j]|` times in all, `|cells[j]|` the distinct cells of component `j`, at
                // most the tuple types times the components. Proof: (1) each pass that goes back
                // closes a cell that was open: `take_out_piece` closes the cell of the piece it
                // takes, open when it was tried, since every try since restored what it changed;
                // `nested_cover` takes out a piece only if it takes out the first of its order, a
                // piece whose set `H` of cells holding it is a largest one. The cells are nested
                // or disjoint (`nested_pieces` gives `None` when two cross), so the cells of `H`,
                // which all hold that piece, form a chain; let `c` be its innermost cell. Every
                // piece `c` holds is held by each cell of `H`, so its set of cells holds `H`, and
                // being no larger it is `H`: `c` is counted once, its count falls to 0 and
                // `close(j, c, true)` runs. (2) Nothing in this loop
                // opens a cell again: `narrow_tuples` only closes cells and shrinks components,
                // and every `restore` here, in `take_out_piece` and in `nested_cover` goes back to
                // a mark taken in the same pass. So the passes are at most the open cells plus
                // the last one. Each pass narrows the part order `C` times for `C` open cells (once
                // at the top, at most `2 m + 1` times in `nested_cover` for its component's `m`
                // cells, `2 C` in `take_out_piece`) and runs `nested_pieces`' `O(m²)` emptiness
                // tests of single cells, so the loop costs at most order `C² n + C m²` for a
                // part of `n` nodes. Measured
                // (2026-11-15, not kept): no family reached a third pass. `n` rows against a
                // chain of shapes `((#_, int), i | i + 1)`, two passes per frame; one row
                // `(#_, 0 | … | m)` against `(#_ \ #c_i, i | i + 1)`, one pass. In that row's
                // pass every piece rests on a fork, and `take_out_piece` alone tried every cell
                // before it took a forked piece, order `C n` (73.7 times the instructions at 8
                // times `m`); `take_out_points`, tried first, takes the fork-free pieces in
                // groups (8.96 times, PERF-take-out-forked-scan). COMPLEXITY.md K118.
                if self.nested_cover(g, &f, &open).await || self.take_out_piece(g, &f, &open).await
                {
                    continue;
                }
                let mut all_empty = true;
                let mut forks = Vec::new();
                let mut blamed_false = Vec::new();
                for &k in &open {
                    let mark = g.log.len();
                    let holds_mark = g.forked_holds.len();
                    for j in 0..g.r.len() {
                        if g.is_open(k, j) {
                            let t = &g.r[j] & &g.atoms[k][j];
                            g.shrink(j, t);
                            g.close(j, g.cell(k, j), false);
                        }
                    }
                    let snap = self.fork_snapshot();
                    let (b, back) = self.tuples(std::mem::take(g), f.clone(), false).await;
                    *g = back;
                    g.forked_holds.truncate(holds_mark);
                    g.restore(mark);
                    if !b {
                        all_empty = false;
                        match self.take_blame_on_false(snap, None) {
                            None => return false,
                            Some(gu) => blamed_false.push(gu),
                        }
                        continue;
                    }
                    if let Some(fork) = self.take_fork(snap, None) {
                        forks.push(fork);
                    }
                }
                if !all_empty {
                    for gu in blamed_false {
                        self.restore_fork(gu);
                    }
                    return false;
                }
                for fork in forks {
                    self.restore_fork(fork);
                }
                return true;
            }
            // The passes this goes back for are bounded with those of the `may_cover` branch
            // above: each closes an open cell and none opens one, so at most `1 + Σ_j
            // |cells[j]|` passes in all (PERF-take-out-piece-chain).
            if self.take_out_piece(g, &f, &open).await {
                continue;
            }
            if !g.forked_holds.is_empty() {
                let mark = g.log.len();
                for idx in 0..g.forked_holds.len() {
                    let (j, c, _) = g.forked_holds[idx];
                    if g.cells[j][c].open {
                        g.close(j, c, false);
                    }
                }
                let empty_on_fork = f.restrict(&|a| g.stand(a)).settle().is_leaf() == Some(false);
                g.restore(mark);
                if empty_on_fork {
                    for (_, _, fork) in std::mem::take(&mut g.forked_holds) {
                        self.restore_fork(fork);
                    }
                    return true;
                }
            }
            // Complexity tradeoff: a tuple part that neither narrowing, nor the split by class,
            // nor one split per branch into its open tuple types, nor one cut of a component
            // decides counts as inhabited for `is_empty`, and `verdict` answers
            // `Refused(TupleSplit)` unless `Searching::refine` finds a value first; the checker
            // adds the cause to the rejection. Why: emptiness of Boolean combinations of tuple
            // types is coNP-hard (a cover of the box by tuple types is a DNF tautology), and one
            // split per branch keeps the search polynomial. Trigger: a part that only a split of
            // the box in two or more components at once proves empty. Tests:
            // `l01_23_groups_and_refusals::refusals::each_refusal_names_its_cause` (`box_cover`),
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
    /// against it costs the size of the class, not of the component; but when `f` holds no tuple
    /// outside the classes' tuple types, the box keeps the component as it is, which then adds
    /// no tuple of the piece's part, and a test costs what it costs in `g`. `each` is done with
    /// the box and the part of each piece whose part is not `false`, and answers whether to go
    /// on.
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
        // Each tuple type's classes, in increasing order: one for the classes of `overlaps`,
        // one or more for the pieces of `key_pieces`.
        let mut class_of: DigestMap<usize, Vec<usize>> = DigestMap::default();
        for (i, (_, ks)) in classes.iter().enumerate() {
            for &k in ks {
                class_of.entry(k).or_default().push(i);
            }
        }
        let at = |a: &Row| class_of.get(&g.index[a]);
        // Whether a tuple type of classes `is` has one in `this`: one binary search.
        let within = |is: &[usize], this: &Range<usize>| {
            is.get(is.partition_point(|&i| i < this.start))
                .is_some_and(|&i| i < this.end)
        };
        let mut forks = Vec::new();
        let out = f.restrict(&|a| at(a).map(|_| false));
        // Complexity tradeoff (PERF-types-cut-rows-union-scaling): naive, each class's piece
        // keeps in component `j` only the union of the class's cells, so every test of a cell
        // of the piece against its box reads that union: a class of `n` cells over a component
        // the cells do not narrow costs order `n` per test and `n²` for its piece (`n` rows
        // `((#_, i) \ (#a, i), 3)` against `((#_, int), 3) | (1, 2)`, one class of the nested
        // sets and one of `1`: 5.21G instructions at n 128, 48.9 times n 16). Used: when `f`
        // is `false` with every tuple type of every class taken out (`out`), the piece keeps
        // the component as it is, whose tests cost what they cost in this box: 73.4M
        // instructions at n 128, 7.4 times. Proof that the answer is the same: each tuple type
        // of `f` is open on `j` and in one class (`classes`), so at a tuple whose component
        // `j` lies in no cell of the class, the class's tuple types are false there, and the
        // other classes' are taken out of the piece's part; the part is then `out`, `false`,
        // so the values the wider box adds hold no tuple of the part, and the piece is empty,
        // or holds a value (`Each::Seek`), exactly when it is on the class's box. A tuple whose
        // component `j` lies in a cell of the class meets no cell of another class, so the
        // piece's part agrees with `f` there. Given up: when `out` is not `false` (the rest of
        // the component is then empty, or the rest's piece has answered), the meet is kept, so
        // a large class over such a box still costs its size per test. The proof needs each
        // tuple type in one class; a piece of `key_pieces` whose tuple types are also in other
        // pieces keeps only its own values, a finite set of keys.
        let wide = out.is_leaf() == Some(false) && class_of.values().all(|is| is.len() == 1);
        if !wide {
            let met = Type::union_all(classes.iter().map(|(c, _)| c.clone()));
            let rest = &g.r[j] - &met;
            match self.empty_fork(&rest).await {
                (false, _) => {
                    let mut r = g.r.clone();
                    r[j] = rest;
                    let snap = self.fork_snapshot();
                    if !self.each(each, r, out).await {
                        return false;
                    }
                    if let Some(fork) = self.take_fork(snap, None) {
                        forks.push(fork);
                    }
                }
                (true, Some(fork)) => forks.push(fork),
                (true, None) => {}
            }
        }
        // Each entry: the part of the halves above, the classes of this half, and whether the
        // tuple types with no class in this half are to be taken out of the part (not at the
        // top). Each tuple type is then in the parts of the halves that hold one of its
        // classes, `O(s log k)` of them for `s` classes of `k`.
        let mut halves = vec![(f.clone(), 0..classes.len(), false)];
        while let Some((f, this, cut)) = halves.pop() {
            let f = match cut {
                false => f,
                true => {
                    let f = f.restrict(&|a| at(a).filter(|is| !within(is, &this)).map(|_| false));
                    if f.is_leaf() == Some(false) {
                        continue;
                    }
                    f
                }
            };
            if this.len() == 1 {
                let mut r = g.r.clone();
                if !wide {
                    r[j] = &r[j] & &classes[this.start].0;
                }
                if f.is_leaf() != Some(false) {
                    let snap = self.fork_snapshot();
                    if !self.each(each, r, f).await {
                        return false;
                    }
                    if let Some(fork) = self.take_fork(snap, None) {
                        forks.push(fork);
                    }
                }
                continue;
            }
            let m = this.start + this.len() / 2;
            halves.push((f.clone(), m..this.end, true));
            halves.push((f, this.start..m, true));
        }
        for fork in forks {
            self.restore_fork(fork);
        }
        true
    }

    /// Does `each` with the piece of the box `r` and its part `f`, and answers whether to go on.
    async fn each(&'m self, each: &mut Each<'_>, r: Vec<Type>, f: Part<Row>) -> bool {
        match each {
            Each::Decide { may_cover } => self.piece(r, f, *may_cover).await,
            Each::Narrow { failed } => {
                if f.is_leaf() == Some(false) {
                    return true;
                }
                let snap = self.fork_snapshot();
                let mut h = self.region(r, &f).await;
                if self.narrow_tuples(&mut h, &mut f.clone()).await
                    && self.take_fork(snap, None).is_none()
                {
                    return true;
                }
                self.discard_since(snap);
                **failed = true;
                false
            }
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

    /// The tuple part `f` on the box of `g` decided in one pass over its nodes (step
    /// EMPTY-overlap-chain), when each open tuple type of `open` is open on one component alone
    /// and the open cells of each component share no value: a tuple of the box then has on each
    /// component a value of one open cell, or of none when the component has such a value, and
    /// is in the tuple types of the cells of its values and no others. So the part is a
    /// function of one choice per component, and [`Choices::decide`] reads it so. `None` when
    /// the part is not of that structure ([`Searching::layout`]); else whether no tuple of the
    /// box is in `f`, or `Err` with the component of a meet `Choices` does not read.
    async fn one_pass(
        &'m self,
        g: &Region,
        f: &Part<Row>,
        open: &[usize],
    ) -> Option<Result<bool, usize>> {
        let l = self.layout(g, open).await?;
        let at = |a: &Row| l.at[g.index[a]].expect("an atom of the part is open");
        Some(l.choices(&at).decide(f).map(|inhabited| !inhabited))
    }

    /// A box inside the tuple part `f` and the box of `g`, read off the choice on each component
    /// that [`Choices::witness`] finds (step EMPTY-overlap-fast): a component chosen at a cell is
    /// narrowed to that cell, and one chosen at a value of no open cell to the values outside
    /// them. `None` when the part is not of the structure of [`Searching::one_pass`] or the pass
    /// does not decide it; `Some(None)` when no tuple of the box is in `f`. So a value of such
    /// a part costs one pass, not a search for each tuple type.
    async fn one_pass_row(
        &'m self,
        g: &Region,
        f: &Part<Row>,
        open: &[usize],
    ) -> Option<Option<Vec<Type>>> {
        let l = self.layout(g, open).await?;
        let at = |a: &Row| l.at[g.index[a]].expect("an atom of the part is open");
        let picks = l.choices(&at).witness(f).ok()?;
        Some(picks.map(|picks| {
            (picks.iter().enumerate())
                .map(|(j, pick)| match pick {
                    Some(Choice::Cell(c)) => &g.r[j] & &g.cells[j][*c].ty,
                    Some(Choice::Other) => l.rest[j].clone(),
                    None => g.r[j].clone(),
                })
                .collect()
        }))
    }

    /// For [`Searching::one_pass`]: the component and cell of each open tuple type of `open`,
    /// and each component's open cells and the values of the box outside them; `None` when an
    /// open tuple type is open on two components or misses one, or when two open cells of a
    /// component may share a value. Each component is compared with the union of its open cells
    /// once.
    async fn layout(&'m self, g: &Region, open: &[usize]) -> Option<Layout> {
        let mut at: Vec<Option<(usize, usize)>> = vec![None; g.atoms.len()];
        let mut cells: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
        for &k in open {
            let (loose, j) = g.loose[k];
            if g.missed[k] != 0 || loose != 1 {
                return None;
            }
            let c = g.cell(k, j);
            at[k] = Some((j, c));
            cells.entry(j).or_default().insert(c);
        }
        let n = g.r.len();
        let mut l = Layout {
            at,
            count: vec![0; n],
            other: vec![false; n],
            cells: vec![Vec::new(); n],
            rest: g.r.clone(),
        };
        for (j, cs) in cells {
            // Two cells that may share a value, as the split into classes reads them (K36),
            // leave the part to the search.
            let groups = overlaps(cs.iter().map(|&c| &g.cells[j][c].ty));
            if groups.iter().any(|is| is.len() > 1) {
                return None;
            }
            let union = Type::union_all(cs.iter().map(|&c| g.cells[j][c].ty.clone()));
            l.rest[j] = &g.r[j] - &union;
            l.other[j] = !self.empty(&l.rest[j]).await;
            l.count[j] = cs.len();
            l.cells[j] = cs.into_iter().collect();
        }
        Some(l)
    }

    /// Takes out of the box `g`, on the first component that lists finitely many literals, on
    /// which every tuple type of `open` is open with a cell that lists finitely many literals
    /// too, every piece `a & r` (the meet of the component `r` with an open cell `a`) on which
    /// narrowing alone proves `f` empty with no fork, and whether it took one out. The pieces
    /// are tested in groups: their order by first point is halved, and for a group's union `U`
    /// the part is restricted from its parent group's part to the tuple types whose cell meets
    /// `U`. A group whose restricted part is `false` is taken out whole with no narrowing; a
    /// group of more than one piece whose part is not `false` is halved; a single piece is
    /// narrowed on the box with the component set to its points, and taken out when that
    /// proves it empty with no fork.
    ///
    /// Proof that this takes out what DESIGN.md L1.23 takes out: a tuple type whose cell
    /// misses `U` misses the box, so it is false there and restricting it to `false` is
    /// narrowing's own first step. A group whose part is `false` is a union of pieces, each
    /// within `U`, on each of which that first step alone leaves `false`, so narrowing proves
    /// each of them empty with no fork (narrowing is monotone, the proof at `nested_cover`),
    /// and DESIGN takes each out; once some are out, each other is the meet of its cell with
    /// the box as it then stands, within the piece proved, so proved too. Taking out `U` whole
    /// is therefore taking out those pieces one after another. Sound whatever the order: no
    /// tuple of `U` is in `f`. A piece whose proof rests on a fork is not taken here, so the
    /// loop below still takes such a piece only when no piece's proof is fork-free.
    ///
    /// Complexity tradeoff (PERF-take-out-forked-scan, COMPLEXITY.md K118): naive, the loop
    /// below narrows the whole part once per piece it tries, order `C n` per pass for `C` open
    /// cells, and taking out `C` pieces one by one costs `C` such narrowings: a row
    /// `(#_, 0 | … | m)` against `m` shapes `(q_i, i | i + 1)` cost 11.9M and 878M
    /// instructions at `m` 16 and 128 (73.6 times at 8 times `m`, limit 10.5). Used: the
    /// halving above. A tuple type is in the part of a group only when its cell meets the
    /// group's union, and each group is restricted from its parent's part, so a level of the
    /// halving reads the parts of the level above; when each cell meets the unions of `O(1)`
    /// groups per level, as cells of `O(1)` points in point order do, the parts of one level
    /// sum to order `n` and the `O(log C)` levels to `n log C`, against `C n`. Finding the
    /// points costs the literals the cells list, times `log P` for `P` points. Only single
    /// pieces are narrowed, so at most `C` narrowings run, each on a part restricted to the
    /// tuple types meeting that piece. Given up: a cell meeting most groups' unions, such as
    /// one holding all points but one, is in most groups' parts, so no group above single
    /// pieces is `false` and each of the `C` single pieces is narrowed on a part holding that
    /// cell, up to order `C n`, the naive order, before the loop below runs. Tests:
    /// `l01_23_groups_and_refusals::judgments::bench::a_row_against_shapes_whose_pieces_all_rest_on_forks_is_decided_in_linear_time`.
    async fn take_out_points(&'m self, g: &mut Region, f: &Part<Row>, open: &[usize]) -> bool {
        let held = Held::default();
        'component: for j in 0..g.r.len() {
            if open.iter().any(|&k| !g.is_open(k, j)) {
                continue;
            }
            let Some(points) = literal_keys(g.r[j].p_held(&held)) else {
                continue;
            };
            let at: BTreeMap<&Key, usize> =
                points.iter().enumerate().map(|(i, p)| (p, i)).collect();
            // For each point, the open cells holding it; for each distinct piece, its points in
            // order and the cells whose meet with the component it is.
            let mut cells_at: Vec<Vec<usize>> = vec![Vec::new(); points.len()];
            let mut pieces: BTreeMap<Vec<usize>, Vec<usize>> = BTreeMap::new();
            for c in g.open_cells(j, open) {
                let Some(keys) = literal_keys(g.cells[j][c].ty.p_held(&held)) else {
                    continue 'component;
                };
                // `keys` is in order, so the points are too.
                let ps: Vec<usize> = keys.iter().filter_map(|k| at.get(k).copied()).collect();
                for &p in &ps {
                    cells_at[p].push(c);
                }
                pieces.entry(ps).or_default().push(c);
            }
            let pieces: Vec<(Vec<usize>, Vec<usize>)> = pieces.into_iter().collect();
            if pieces.is_empty() {
                continue;
            }
            let mut out: BTreeSet<usize> = BTreeSet::new();
            let mut halves = vec![(f.clone(), 0..pieces.len())];
            while let Some((part, this)) = halves.pop() {
                let u: BTreeSet<usize> = pieces[this.clone()]
                    .iter()
                    .flat_map(|(ps, _)| ps.iter().copied())
                    .collect();
                if u.iter().all(|p| out.contains(p)) {
                    continue;
                }
                let meets: BTreeSet<usize> = u
                    .iter()
                    .flat_map(|&p| &cells_at[p])
                    .flat_map(|&c| g.cells[j][c].rows.iter().copied())
                    .collect();
                let part = part.restrict(&|a| (!meets.contains(&g.index[a])).then_some(false));
                let proved = if part.is_leaf() == Some(false) {
                    true
                } else if this.len() > 1 {
                    false
                } else {
                    let mut r = g.r.clone();
                    r[j] = Type::union_all(u.iter().map(|&p| key_type(&points[p])));
                    let snap = self.fork_snapshot();
                    let mut h = self.region(r, &part).await;
                    let hit = self.narrow_tuples(&mut h, &mut part.clone()).await;
                    let proved = hit && self.take_fork(snap, None).is_none();
                    if !proved {
                        self.discard_since(snap);
                    }
                    proved
                };
                if proved {
                    out.extend(u);
                } else if this.len() > 1 {
                    let m = this.start + this.len() / 2;
                    halves.push((part.clone(), m..this.end));
                    halves.push((part, this.start..m));
                }
            }
            if out.is_empty() {
                continue;
            }
            let gone = Type::union_all(out.iter().map(|&p| key_type(&points[p])));
            let left = &g.r[j] - &gone;
            g.shrink(j, left);
            // A cell all of whose points are out misses the component now.
            for (ps, cs) in &pieces {
                if ps.iter().all(|p| out.contains(p)) {
                    for &c in cs {
                        g.close(j, c, true);
                    }
                }
            }
            return true;
        }
        false
    }

    /// Takes out of the box `g` the pieces of one component, each cut by an open cell of the
    /// tuple types `open` (its meet with the component or what the component holds outside it),
    /// on which narrowing alone proves `f` empty (DESIGN.md L1.23), and whether it took one out.
    /// A piece whose proof rests on a fork is taken out only when no piece's proof is fork-free.
    ///
    /// Complexity tradeoff: the components are tried in the order of their open cells, fewest
    /// first, and after the first component a piece was taken out of the caller narrows the box
    /// left again. Why: a box whose few-celled component holds the piece to take out, beside a
    /// component of `n` cells, is decided by a narrowing of the part of `n` nodes per piece of
    /// the few-celled component, order `n`. Trying the components in their written order,
    /// the `n`-celled one first, also stayed linear on the bench below but cost 2.3 times the
    /// instructions (148M and 1.18G at `n` 128 and 1,024, against 64M and 505M), measured
    /// once as a negative control and not kept. A pass that takes nothing
    /// out narrows the part twice per open cell of the box, as before, order `C n` for `C` open
    /// cells, the order of the split into the open tuple types it comes before. Test:
    /// `l01_23_groups_and_refusals::judgments::bench::crossing_sets_against_a_wider_second_component_are_decided_in_linear_time`.
    /// COMPLEXITY.md K118.
    async fn take_out_piece(&'m self, g: &mut Region, f: &Part<Row>, open: &[usize]) -> bool {
        if self.take_out_points(g, f, open).await {
            return true;
        }
        let mut order: Vec<(usize, BTreeSet<usize>)> =
            (0..g.r.len()).map(|j| (j, g.open_cells(j, open))).collect();
        order.sort_by_key(|(j, cells)| (cells.len(), *j));
        let mut forked_cut = None;
        for (j, cells) in order {
            let mut tried = BTreeSet::new();
            let mut taken = false;
            // A cell closed on the component misses or holds it, so its pieces are the
            // component and nothing, and narrow nothing.
            for cell in cells {
                if !g.cells[j][cell].open {
                    continue;
                }
                let a = g.cells[j][cell].ty.clone();
                for (c, missed) in [(&a & &g.r[j], false), (&g.r[j] - &a, true)] {
                    if tried.contains(&c) {
                        continue;
                    }
                    let cut_snap = self.fork_snapshot();
                    if self.empty_fork(&c).await.0 || self.empty_fork(&(&g.r[j] - &c)).await.0 {
                        self.discard_since(cut_snap);
                        continue;
                    }
                    tried.insert(c.clone());
                    let mark = g.log.len();
                    let holds_mark = g.forked_holds.len();
                    g.shrink(j, c.clone());
                    g.close(j, cell, missed);
                    let snap = self.fork_snapshot();
                    let hit = self.narrow_tuples(g, &mut f.clone()).await;
                    g.forked_holds.truncate(holds_mark);
                    g.restore(mark);
                    if hit {
                        match self.take_fork(snap, None) {
                            None => {
                                let t = &g.r[j] - &c;
                                g.shrink(j, t);
                                g.close(j, cell, !missed);
                                taken = true;
                                break;
                            }
                            Some(fork) => {
                                self.discard_since(cut_snap);
                                forked_cut.get_or_insert((j, c, cell, missed, fork));
                            }
                        }
                    } else {
                        self.discard_since(cut_snap);
                    }
                }
            }
            if taken {
                return true;
            }
        }
        let Some((j, c, cell, missed, fork)) = forked_cut else {
            return false;
        };
        self.restore_fork(fork);
        let t = &g.r[j] - &c;
        g.shrink(j, t);
        g.close(j, cell, !missed);
        true
    }

    /// Whether no tuple in the box `r` is in `f`, decided on a region of its own.
    async fn piece(&'m self, r: Vec<Type>, f: Part<Row>, may_cover: bool) -> bool {
        if f.is_leaf() == Some(false) {
            return true;
        }
        let h = self.region(r, &f).await;
        self.tuples(h, f, may_cover).await.0
    }

    /// Takes out of the box `g`, one after another and innermost first, the pieces of one
    /// component cut by its open cells (`nested_pieces`) on which narrowing alone proves `f`
    /// empty, the component with fewest open cells among those on which a tuple type of `open`
    /// is open, and whether it took one out. It stops at the first piece narrowing does not
    /// prove empty, or proves empty only on a fork, and keeps the pieces taken out before it;
    /// the caller narrows the box left, which is the rest of the component once every piece is
    /// out.
    ///
    /// Each piece taken out is the step "each piece on which narrowing alone proves the part
    /// empty is taken out of the box" of DESIGN.md L1.23, on the box as it stands, and the
    /// narrowing run on it is on the very box that step names (TEST-nested-cover-verdict-change,
    /// PROOF-narrow-tuples-monotone). Proof: the cells holding a piece all meet in it, and the
    /// cells are pairwise nested or disjoint, so they are nested, a chain with an innermost
    /// cell `c`. Another piece within `c` is held by `c` and by every cell around `c`, so by
    /// more cells than this piece, and was taken first. The pieces within `c` cover its meet
    /// with the component (`nested_pieces`), so when this piece is reached the meet of `c`
    /// with the box as it stands is this piece: a piece cut by an open tuple type. The
    /// narrowing runs on the box with the component set to the piece and each open cell closed
    /// by whether it holds the piece, each by a test that proved it. The box is the stopped box
    /// less the pieces taken out, and taking out the last piece of a cell closes that cell as
    /// missing the component, whose meet with it is then empty.
    ///
    /// So no answer of `narrow_tuples` on one box is used for another; whether `narrow_tuples`
    /// as written is monotone, with emptiness tests that may decide a type on a box and not on
    /// a smaller one, is not claimed. That the order DESIGN takes the pieces out in, or
    /// narrowing again between them, does not change what DESIGN settles follows from its
    /// narrowing being monotone, in which each tuple type holds, misses or is open on the box
    /// exactly: if narrowing proves the part empty from a box `X`, it proves it from any box
    /// `Y` within `X`. Proof: let `X = X0, X1, …, Xn` be the boxes `X`'s narrowing passes
    /// through, the part false on what `Xn` knows or `Xn` empty, and keep `Yi` within `Xi`. A
    /// tuple type that holds or misses `Xi` does the same on `Yi`, so `Yi` knows what `Xi`
    /// knows, and the three-valued evaluation, monotone in what is known, is false on `Yi`
    /// where it is false on `Xi`. A tuple type `T` in every value of the part at `Xi` (the
    /// part false with `T` false) is in every value at `Yi`: if `T` misses `Yi` the part is
    /// false there, else `Yi` narrowed to `T` is within `Xi` narrowed to `T`. A tuple type `T`
    /// in no value at `Xi` holds `Xi` on every component but one, `l`, so it holds `Yi` on
    /// every component but at most `l`: if it holds `Yi` the part is false there, if it misses
    /// `Yi` then `Yi` is within `Xi` less `T`, else `Yi` less `T` on `l` is within `Xi` less
    /// `T` on `l`. At `n` the part is false on `Yn` or `Yn` is empty. Narrowing from `Y` in
    /// its own order stops at a box `Z` within `Y` on which no step changes anything; by the
    /// same cases each step from `X` shows the part false on `Z` or leaves `Z` within the next
    /// box, so the part is false on `Z`. Hence a piece narrowing proves empty on the stopped
    /// box is proved empty on every smaller box the steps reach, and taking pieces out never
    /// undoes another's proof.
    ///
    /// Complexity tradeoff: before the split of the box into its meet with each open tuple type
    /// (K71), the component with fewest open cells is cut into the pieces its cells cut, each
    /// narrowed once. It decides no part that a split in more than one component at once is
    /// needed for: a piece narrowing does not prove empty leaves the box to `take_out_piece`
    /// and the split below. Why: the naive method, the split into the open tuple types, makes
    /// one piece per open tuple type, `k` pieces each narrowing the whole part of `n` nodes
    /// again, order `k n`: `n` rows `((#_, i) \ (#a, i), 1)` against `((#_, int), 1 | 2)` cost
    /// 44.2M, 1.72G and 101.5G instructions at `n` = 16, 128 and 1,024 (38.8 and 59.2 times at
    /// 8 times `n`). The new method makes at most `2 m` pieces for `m` distinct open cells on
    /// the component, `m` at most `k`, each narrowed once, and the caller narrows the rest
    /// once, order `m n`: here `m` is 2 (`1` and `1 | 2`) and the time is linear in `n`.
    /// Finding the pieces costs one or two emptiness tests of single cells per cell disjoint
    /// from the cells before it or holding them all, and two per piece so far for any other
    /// cell, order `m²` at worst. A piece narrowing does not prove empty costs at most the `2 m`
    /// narrowings before the steps below, and each piece taken out closes a cell, so the order
    /// stays `k n`. Soundness: the pieces are pairwise disjoint and cover the cells' meet with
    /// the component (`nested_pieces`), and each lies within or outside each open cell by a
    /// test that proved it, so `close` records exactly whether each tuple type holds or misses
    /// the component there, and narrowing is sound on each piece (`narrow_tuples`); a test not
    /// decided, or a cell meeting two pieces in part, leaves the box to the steps below. Test:
    /// `l01_23_groups_and_refusals::judgments::bench::nested_sets_against_a_wider_second_component_are_decided_in_linear_time`.
    /// COMPLEXITY.md K118.
    async fn nested_cover(&'m self, g: &mut Region, f: &Part<Row>, open: &[usize]) -> bool {
        if NO_NESTED_COVER.with(std::cell::Cell::get) {
            return false;
        }
        let Some(j) = (0..g.r.len())
            .filter(|&j| open.iter().any(|&k| g.is_open(k, j)))
            .min_by_key(|&j| g.open_cells(j, open).len())
        else {
            return false;
        };
        let open_cells = g.open_cells(j, open);
        let split_snap = self.fork_snapshot();
        let Some(pieces) = self.nested_pieces(g, j, &open_cells).await else {
            self.discard_since(split_snap);
            return false;
        };
        // One piece for each set of cells holding it, innermost first: a piece held by more
        // cells lies within the cell of each piece held by fewer that it meets.
        let mut by_held: BTreeMap<BTreeSet<usize>, Type> = BTreeMap::new();
        let mut left: BTreeMap<usize, usize> = BTreeMap::new();
        for (p, held) in pieces {
            if let Some(t) = by_held.get_mut(&held) {
                // Not reached: no two pieces are held by the same cells. In `laminar_pieces`
                // the piece of cell `c` is held by `c`'s own cells and those of the cells around
                // it; two pieces of one set would have each cell inside the other, which a
                // forest of cells does not have. In `pieces_one_at_a_time`, by induction over
                // the cells added: a cell's own cells `cs` are new and not empty, so `t - u`
                // (held by `cs` alone) differs from each piece held before (each holds an
                // earlier cell), a piece `p` cut into `p - t` and `p & t` gives `held(p)` and
                // `held(p) ∪ cs`, which differ, and adding `cs` to two pieces of different
                // sets keeps them different, `cs` holding no earlier cell. Kept, joining the
                // two, so that the answer holds whatever the pieces.
                debug_assert!(false, "two pieces held by the same cells");
                *t = &*t | &p;
                continue;
            }
            for &c in &held {
                *left.entry(c).or_default() += 1;
            }
            by_held.insert(held, p);
        }
        let mut order: Vec<(BTreeSet<usize>, Type)> = by_held.into_iter().collect();
        order.sort_by_key(|(held, _)| std::cmp::Reverse(held.len()));
        let mut taken = false;
        for (held, p) in order {
            let mark = g.log.len();
            let holds_mark = g.forked_holds.len();
            g.shrink(j, p.clone());
            for &cell in &open_cells {
                if g.cells[j][cell].open {
                    g.close(j, cell, !held.contains(&cell));
                }
            }
            let snap = self.fork_snapshot();
            let hit = self.narrow_tuples(g, &mut f.clone()).await;
            g.forked_holds.truncate(holds_mark);
            g.restore(mark);
            // A proof resting on a fork is left to `take_out_piece`, which takes such a piece
            // out only when no piece's proof is fork-free.
            if !hit || self.take_fork(snap, None).is_some() {
                self.discard_since(snap);
                break;
            }
            let t = &g.r[j] - &p;
            g.shrink(j, t);
            for &cell in &held {
                let n = left
                    .get_mut(&cell)
                    .expect("a cell holding a piece is counted");
                *n -= 1;
                if *n == 0 {
                    g.close(j, cell, true);
                }
            }
            taken = true;
        }
        if !taken {
            self.discard_since(split_snap);
        }
        taken
    }

    /// The pieces of component `j` of the box `g` cut by its open cells `open_cells`, each with
    /// the cells holding it (it misses the others), in the order of their types; `None` when
    /// two cells cross (neither is within the other and they meet), a cell meets two pieces
    /// cut so far in part, or a test is not decided.
    /// Each distinct cell `t` is added to the pieces of the cells before it, of union `u`: when
    /// `t & u` is empty, `t` is a piece; else when `u - t` is empty, every piece lies within
    /// `t`; else each piece `p` lies outside `t`, within it, or is cut into `p & t` and `p - t`;
    /// then `t - u`, unless empty, is a piece. So the pieces stay pairwise disjoint, cover `u`,
    /// and each lies within or outside each cell added. Nested or disjoint cells never meet
    /// two pieces in part, and since a cell cuts at most one piece and adds at most one, `m`
    /// distinct cells give at most `2 m` pieces.
    async fn nested_pieces(
        &'m self,
        g: &Region,
        j: usize,
        open_cells: &BTreeSet<usize>,
    ) -> Option<Vec<(Type, BTreeSet<usize>)>> {
        let mut types: Vec<(Type, BTreeSet<usize>)> = Vec::new();
        let mut seen: BTreeMap<Type, usize> = BTreeMap::new();
        for &c in open_cells {
            let t = &g.cells[j][c].ty & &g.r[j];
            match seen.get(&t) {
                Some(&i) => {
                    types[i].1.insert(c);
                }
                None => {
                    seen.insert(t.clone(), types.len());
                    types.push((t, BTreeSet::from([c])));
                }
            }
        }
        let laminar = self.laminar_pieces(&types).await;
        if PIECES_COMPARED.with(std::cell::Cell::get) {
            let one = self.pieces_one_at_a_time(types).await;
            if let Some(found) = laminar {
                assert_eq!(
                    found, one,
                    "the pieces found two at a time and one at a time differ"
                );
            }
            return one;
        }
        match laminar {
            Some(found) => found,
            None => self.pieces_one_at_a_time(types).await,
        }
    }

    /// The pieces of [`Searching::nested_pieces`] for the distinct cells `types`, cut one cell
    /// at a time. Reached in product code only when [`Searching::laminar_pieces`] meets a test
    /// not decided.
    async fn pieces_one_at_a_time(
        &'m self,
        types: Vec<(Type, BTreeSet<usize>)>,
    ) -> Option<Vec<(Type, BTreeSet<usize>)>> {
        // Only cells pairwise nested or disjoint on the component are cut here: DESIGN (sec.
        // L1.23) takes out of the box "each piece on which narrowing alone proves the part
        // empty", a piece being the meet of the component with one open tuple type's cell, so
        // a piece inside two crossing cells (`0 | 1` and `1 | 2` give `1`) is no such piece,
        // and a box only such pieces settle is one DESIGN counts as inhabited unless a later
        // step settles it. In a family of cells pairwise nested or disjoint, each piece cut
        // below is a cell less the cells inside it, and `nested_cover` takes them out innermost
        // first, so each is a cell's meet with the box as it stands when it is taken out (the
        // proof is at `nested_cover`). Crossing cells, or a test not decided, leave the box to
        // the steps below. Whether a cell crosses one before it is read off the pieces, each within or
        // outside each earlier cell, so it takes no emptiness test beyond those of the cut
        // and costs set operations on the cells the pieces hold.
        let mut pieces: Vec<(Type, BTreeSet<usize>)> = Vec::new();
        let mut union = Type::empty();
        let mut rest_empty: Option<bool> = None;
        for (t, cs) in types {
            if self.shown(&(&t & &union)).await == Some(true) {
                union = &union | &t;
                pieces.push((t, cs));
                continue;
            }
            if self.shown(&(&union - &t)).await == Some(true) {
                for (_, held) in &mut pieces {
                    held.extend(&cs);
                }
            } else {
                rest_empty = Some(self.shown(&(&t - &union)).await?);
                let mut cut = None;
                // The cells held by a piece `t` meets, by one it misses or cuts, and by every
                // piece it meets.
                let (mut met, mut outside, mut every) = (BTreeSet::new(), BTreeSet::new(), None);
                for (i, (p, held)) in pieces.iter_mut().enumerate() {
                    if self.shown(&(&*p & &t)).await? {
                        outside.extend(held.iter().copied());
                        continue;
                    }
                    met.extend(held.iter().copied());
                    let common = every.get_or_insert_with(|| held.clone());
                    common.retain(|c| held.contains(c));
                    if self.shown(&(&*p - &t)).await? {
                        held.extend(&cs);
                        continue;
                    }
                    outside.extend(held.iter().copied());
                    if cut.replace(i).is_some() {
                        return None;
                    }
                }
                // A cell `c` crosses `t` when `t` meets it, it is not within `t` (a piece it
                // holds is missed or cut by `t`), and `t` is not within it (a piece `t` meets
                // misses it, or `t` holds more than the cells before it).
                let every = every.unwrap_or_default();
                if met
                    .intersection(&outside)
                    .any(|c| !every.contains(c) || rest_empty == Some(false))
                {
                    return None;
                }
                if let Some(i) = cut {
                    let (p, held) = &pieces[i];
                    let mut within = held.clone();
                    within.extend(&cs);
                    let inside = (p & &t, within);
                    pieces[i].0 = &pieces[i].0 - &t;
                    pieces.push(inside);
                }
            }
            let rest_empty = match rest_empty.take() {
                Some(e) => e,
                None => self.shown(&(&t - &union)).await?,
            };
            if !rest_empty {
                pieces.push((&t - &union, cs));
            }
            union = &union | &t;
        }
        pieces.sort_by(|a, b| a.0.cmp(&b.0));
        Some(pieces)
    }

    /// The pieces `nested_pieces` gives for the distinct cells `types`, each with the cells
    /// holding it, found from the cells two at a time: `Some(Some(_))` when the cells are
    /// pairwise nested or disjoint, `Some(None)` when two cross, `None` when a test is not
    /// decided (`nested_pieces` then cuts the pieces one cell at a time).
    ///
    /// Two cells shown apart by their keys ([`meeting_pairs`]) are disjoint; every other pair
    /// is tested: disjoint, the first within the second, the second within the first, or
    /// crossing. Two equal cells count the later one within the earlier. Each cell within
    /// another meets it, so it is inhabited, and the cells holding it meet each other, so each
    /// such pair was tested and found nested: they form a chain, each holding all those outside
    /// it, and its parent, the smallest, is the one held by the most. The piece of a cell is the
    /// cell less its children, left out when shown empty, and is held by the cell and every cell
    /// around it, and missed by the rest: a cell meeting it meets the cell, so is nested with
    /// it, and one inside the cell is inside a child. The pieces are pairwise disjoint and cover
    /// the cells, as those `nested_pieces` cuts one cell at a time are, so they are the same
    /// sets with the same cells holding them: the same pieces, each written as its cell less
    /// its children.
    ///
    /// Complexity tradeoff (PERF-disjoint-rows-shared-shapes): `nested_pieces` cuts the pieces
    /// one cell at a time, testing each new cell against the union of those before it and
    /// against each piece so far, so `m` cells take order `m²` emptiness tests, and the union
    /// and the pieces grow with the cells: `m` rows `((#_, i) \ (#a, i), 0)` against the shapes
    /// `((#_, int), i | i + 1)` put `m` disjoint cells and one around them all on the first
    /// component, each test a search over up to `m` cells, 1.15G and 285G instructions at
    /// `m` = 32 and 256 (248 times at 8 times `m`). Here each test is of two cells, and only
    /// the pairs that share a key are tested: order `p` small tests for `p` such pairs, `p`
    /// the `m` pairs of the outer cell with each row here, plus one test of each cell less its
    /// children, and the keys cost the size of the cells. Worst case: every pair shares a key,
    /// `m²/2` tests of two cells, the order of the cut one cell at a time. With this, the
    /// literal filing in `ByName` and the keyed pairs, that family takes 50.2M and 630M
    /// instructions at `m` 32 and 256 (12.56 times, load 44): still over 10.5, from the
    /// narrowing of each piece against the whole part at `nested_cover` (plan row
    /// PERF-nested-cover-narrow-per-piece, which holds the scaling test). COMPLEXITY.md K118.
    async fn laminar_pieces(
        &'m self,
        types: &[(Type, BTreeSet<usize>)],
    ) -> Option<Option<Vec<(Type, BTreeSet<usize>)>>> {
        let n = types.len();
        let ts: Vec<&Type> = types.iter().map(|(t, _)| t).collect();
        // `outside[a]`: the cells `a` is within (the later of two equal cells is within the
        // earlier).
        let mut outside: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (a, b) in meeting_pairs(&ts) {
            if self.shown(&(ts[a] & ts[b])).await? {
                continue;
            }
            let a_within = self.shown(&(ts[a] - ts[b])).await?;
            let b_within = self.shown(&(ts[b] - ts[a])).await?;
            match (a_within, b_within) {
                (_, true) => outside[b].push(a),
                (true, false) => outside[a].push(b),
                (false, false) => return Some(None),
            }
        }
        let parent: Vec<Option<usize>> = outside
            .iter()
            .map(|o| o.iter().copied().max_by_key(|&x| outside[x].len()))
            .collect();
        // Answers that are those of one order make `parent` a forest. Inside a search they may
        // not be: a test that reads a type still being decided answers on what is known so far,
        // and is tried again once that type is settled, so cells strictly nested can be read as
        // each within the next round a cycle (cells `cons(int \ 1 \ 2, _)` and `cons(int \ 1,
        // _)` over list definitions, the case of
        // `l01_23_groups_and_refusals::sweep_agreement::the_search_ends_when_cells_are_read_as_nested_in_a_cycle`),
        // and the walk up the cells holding each piece below would never end. Such answers do
        // not describe nested or disjoint cells, so the cells count as crossing and the box is
        // left to the steps after `nested_cover`. Each cell is marked once on the walk up from
        // it and once when its walk reaches a root, order `n` for `n` cells (standing rule
        // P207: every walk up these links keeps a visited set).
        let mut state = vec![0u8; n]; // 0 not seen, 1 on the current walk, 2 reaches a root
        for c in 0..n {
            let mut walk = Vec::new();
            let mut up = Some(c);
            while let Some(p) = up {
                match state[p] {
                    2 => break,
                    1 => return Some(None),
                    _ => {}
                }
                state[p] = 1;
                walk.push(p);
                up = parent[p];
            }
            for p in walk {
                state[p] = 2;
            }
        }
        let mut children: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (c, p) in parent.iter().enumerate() {
            if let Some(p) = *p {
                children[p].push(c);
            }
        }
        let mut pieces = Vec::with_capacity(n);
        for c in 0..n {
            let piece = if children[c].is_empty() {
                ts[c].clone()
            } else {
                let inside = Type::union_all(children[c].iter().map(|&x| ts[x].clone()));
                let piece = ts[c] - &inside;
                if self.shown(&piece).await? {
                    continue;
                }
                piece
            };
            let mut held = types[c].1.clone();
            let mut up = parent[c];
            while let Some(p) = up {
                held.extend(&types[p].1);
                up = parent[p];
            }
            pieces.push((piece, held));
        }
        pieces.sort_by(|a, b| a.0.cmp(&b.0));
        Some(Some(pieces))
    }

    /// Whether `t` is shown empty with no fork, `Some(true)`, or shown inhabited with no
    /// refusal on the way, `Some(false)`; `None` otherwise. Only a proof of emptiness keeps
    /// what it read.
    async fn shown(&'m self, t: &Type) -> Option<bool> {
        let snap = self.fork_snapshot();
        let give_ups = self.s().give_ups;
        let (empty, fork) = self.empty_fork(t).await;
        if empty && fork.is_none() {
            return Some(true);
        }
        let inhabited = !empty && self.s().give_ups == give_ups;
        self.discard_since(snap);
        inhabited.then_some(false)
    }

    /// Whether `m` admits no morphism: a key is promised and not permitted, or promised and no
    /// value can be its. A key is promised only when a value is shown in the type: a type not
    /// proved empty may still be empty, and then the empty morphism is admitted.
    async fn no_morphism(&'m self, m: &Morphism) -> bool {
        self.shown_key(&self.cut(&m.guarantee, &m.permission, Cut::Minus))
            .await
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
        let outer = self.s().current.take();
        let b = self.empty(v).await;
        let Some(i) = self.s().ids.get(v).copied() else {
            self.s().current = outer;
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
        } else if b {
            let mut s = self.s();
            if s.canonical_blame && s.answer[i] && !s.deciding.contains(&i) {
                s.settle(i);
            }
        }
        let mut guard = self.s();
        let s = &mut *guard;
        s.current = outer;
        s.value_reads.insert(i);
        let dead = s.dead.contains(&i);
        if let Some(c) = outer {
            s.add_reader(i, c);
            if dead {
                let ep = s.epoch;
                s.push_read(c, pack_read(i, true), ep);
            } else if s.canonical_blame {
                s.epoch += 1;
                let ep = s.epoch;
                s.push_read(c, pack_read(i, false), ep);
            }
        }
        dead
    }

    /// The meet of pure cycles that `t` is, when `t` is a stop atom or not, and a link atom
    /// whose rest is the meet of pure cycles, or their union, less some, all of one item.
    async fn cycle_meet(&'m self, t: &Type) -> Option<Meet> {
        let p = t.p();
        if p.structs || p.tuples.rest || !p.tuples.lens.is_empty() || !only_atoms(&p) {
            return None;
        }
        if p.atoms.names().len() > 2 || p.atoms.cofinite() {
            return None;
        }
        let (mut bare, mut link) = (None, None);
        for (name, a) in p.atoms.names() {
            match (a.bare, a.payload == Type::empty()) {
                (true, true) if bare.is_none() => bare = Some(name.clone()),
                // Never met: the atoms are finite (tested above), and `Atoms::set`, the one
                // writer of `names` (its fields are private to module `types::atoms`, so the
                // compiler checks this), keeps no name whose part is `AtomPart::none()` there.
                (false, true) => unreachable!("a finite atoms map lists a name with no part"),
                (false, false) if link.is_none() => link = Some((name.clone(), a.payload.clone())),
                _ => return None,
            }
        }
        let (name, payload) = link?;
        let q = payload.p();
        if q.structs || q.tuples.rest || q.tuples.lens.len() != 1 || !q.tuples.lens.contains_key(&2)
        {
            return None;
        }
        let f = &q.tuples.lens[&2];
        let (taken, refused) = f.forced();
        // Complexity tradeoff: `f.distinct_atoms()` and `f.eval(...)` walk the diagram `f`, which
        // has `O(n)` nodes on a list difference of `n` rows (`front(n)`, `end(n)`). Most list
        // differences are not pure cycles: their first forced row `a` fails `s.cycle(&a[1])` at
        // once (in `O(log n)` once `cycles` holds `None`). Checking `read(&mut s, a)` on `taken`
        // and `refused` first rejects a non-cycle list in `O(1)` cycle lookups before
        // `f.distinct_atoms()`, and `taken_set: BTreeSet<&Row>` makes `f.eval` `O(k log k)`
        // instead of `O(k^2)`. Nothing is given up: the `Meet` returned is identical.
        if taken.is_empty() && refused.is_empty() {
            return None;
        }
        let item = taken
            .first()
            .or_else(|| refused.first())
            .expect("taken or refused is non-empty")[0]
            .clone();
        let mut stop: Option<std::sync::Arc<str>> = bare;
        let mut read = |s: &mut Search, a: &Row| -> Option<(u64, u64)> {
            let c = s.cycle(&a[1])?;
            let fits = a[0] == item && c.item == item && c.link == name;
            let same = stop.get_or_insert_with(|| c.stop.clone()) == &c.stop;
            // A length one more than a length of the rest.
            (fits && same).then_some((c.period, (c.at + 1) % c.period))
        };
        let mut all = Vec::with_capacity(taken.len());
        let mut none = Vec::with_capacity(refused.len());
        {
            let mut s = self.s();
            for a in &taken {
                all.push(read(&mut s, a)?);
            }
            for a in &refused {
                none.push(read(&mut s, a)?);
            }
        }
        let atoms = f.distinct_atoms();
        if atoms.is_empty() {
            return None;
        }
        let mut any = Vec::new();
        if taken.len() + refused.len() == atoms.len() {
            let taken_set: BTreeSet<&Row> = taken.iter().collect();
            if !f.eval(&|a| taken_set.contains(a)) {
                return None;
            }
        } else {
            // A meet of pure cycles with a union of them, less some: with the rows taken on
            // every path taken and those refused on every path refused, the rest is the union
            // of its rows, and the part is exactly their meet with that union, as it holds no
            // value outside them. One walk of `f`.
            let taken_set: BTreeSet<&Row> = taken.iter().collect();
            let refused_set: BTreeSet<&Row> = refused.iter().collect();
            let rows = f
                .restrict(
                    &|a| match (taken_set.contains(a), refused_set.contains(a)) {
                        (true, _) => Some(true),
                        (_, true) => Some(false),
                        _ => None,
                    },
                )
                .union_rows()?;
            if rows.is_empty() {
                return None;
            }
            let mut s = self.s();
            for a in &rows {
                any.push(read(&mut s, a)?);
            }
        }
        if self.empty(&item).await {
            return None;
        }
        Some(Meet {
            stop: stop?,
            link: name,
            item,
            bare: p.atoms.bare_names() > 0,
            all,
            any,
            none,
        })
    }

    /// The answer for `t`, when `t` is a stop atom or not, and a link atom whose rest is the
    /// meet of pure cycles, or their union, less some, all of one item: the lengths are then
    /// residues, and whether one survives is decided without walking their product.
    async fn pure_cycles(&'m self, t: &Type) -> Option<Lengths> {
        let m = self.cycle_meet(t).await?;
        match m.bare {
            true => Some(Lengths::Some),
            false => Some(m.lengths()?.0),
        }
    }

    /// A list of `m`, of the length `residue_length` gives, kept as that length: the work is
    /// that of the rule on residues, polynomial in the cycles, whatever the length.
    async fn cycle_rep(&'m self, m: &Meet) -> Option<usize> {
        let len = match m.any.is_empty() {
            true => residue_length(&m.all, &m.none)?,
            false => {
                let (lengths, classes) = m.lengths()?;
                if lengths != Lengths::Some {
                    return None;
                }
                residue_length(&classes, &m.none)?
            }
        };
        let item = self.rep(&m.item).await?;
        Some(self.s().show(Rep::List {
            stop: m.stop.clone(),
            link: m.link.clone(),
            item,
            len,
        }))
    }

    /// The front sweep's verdict of `t` alone, or of a single product of sweep-decidable list
    /// types, with every `Inhabited` answer verified by [`Searching::chain_rep`].
    async fn sweep_verdict(&'m self, t: &Type) -> Option<Verdict> {
        let p = t.p();
        if p.bools == 0
            && !p.ints.cofinite
            && p.ints.values.is_empty()
            && !p.rats.cofinite
            && p.rats.values.is_empty()
            && !p.floats.cofinite
            && p.floats.values.is_empty()
            && !p.f32s.cofinite
            && p.f32s.values.is_empty()
            && !p.strings.cofinite
            && p.strings.values.is_empty()
            && !p.structs
            && p.morphisms.is_leaf() == Some(false)
            && !p.atoms.cofinite()
            && p.atoms.names().is_empty()
            && !p.tuples.rest
            && p.tuples.lens.len() == 1
            && let Some(f) = p.tuples.lens.values().next()
            && f.forced().1.is_empty()
            && let Some(rows) = f.union_rows()
            && rows.len() == 1
        {
            let mut all_inhabited = true;
            for c in &rows[0] {
                match Box::pin(self.sweep_verdict(c)).await {
                    Some(Verdict::Empty) => return Some(Verdict::Empty),
                    Some(Verdict::Inhabited) => {}
                    _ => all_inhabited = false,
                }
            }
            return all_inhabited.then_some(Verdict::Inhabited);
        }
        match self.prefix_chains(t).await? {
            ChainPlan::Empty => Some(Verdict::Empty),
            plan @ ChainPlan::Inhabited { .. } => {
                self.chain_rep(t, plan).await.map(|_| Verdict::Inhabited)
            }
        }
    }

    /// Whether `t` is met inside the general fallback of a list (`in_list_fallback`) and is not
    /// an item or a written field within an item (`Search::items`): then neither the front sweep
    /// nor the prefix chains run on it.
    fn in_fallback(&self, t: &Type) -> bool {
        let s = self.s();
        s.in_list_fallback > 0 && !s.items.contains_key(t)
    }

    /// The front sweep's answer ([`sweep::list_sweep_checked`]) for a list type that is one of
    /// the query's own types or a type in their tuple and record fields (`Search::roots`):
    /// `Some(None)` when it is empty, `Some(Some(r))` with `r` its checked value shown. Memoized
    /// per type in `Search::swept`.
    // Complexity tradeoff: the front sweep runs on the roots only, as the prefix chains do
    // (`prefix_chains`), and once per type. Why: `verdict_alone` ran it on the query type
    // alone, so a list in a tuple or record field was left to the general search, which built
    // its value at up to 553 times the work of the list alone (`rec:clstaggerholesout` at 256,
    // R9, X41). Tradeoff: a list type in the sweep's class met only as a type the search builds
    // is left to the search.
    fn swept(&self, t: &Type) -> Option<Option<usize>> {
        if self.in_fallback(t) || t.p().atoms.names().is_empty() || !self.s().roots.contains_key(t)
        {
            return None;
        }
        let known = self.s().swept.get(t).cloned();
        let v = match known {
            Some(v) => v,
            None => {
                let v = sweep::list_sweep_checked(t);
                self.s().swept.insert(t.clone(), v.clone());
                v
            }
        }?;
        let Some(v) = v else {
            return Some(None);
        };
        let mut s = self.s();
        if let Some(Some(r)) = s.reps.get(t).copied() {
            return Some(Some(r));
        }
        let r = s.show(Rep::Value(v));
        let c = s.class(r);
        s.members.insert((c, t.clone()), Some(true));
        s.reps.insert(t.clone(), Some(r));
        Some(Some(r))
    }

    /// Decides `t`, or builds a witness plan for it, when `t` is a list type made of a period-1
    /// carrier cycle and finite prefix chains ending at that carrier (`front` and `far`
    /// families), and `t` is one of the query's own types (`Search::roots`). Memoized per type
    /// in `Search::chains`.
    async fn prefix_chains(&'m self, t: &Type) -> Option<ChainPlan> {
        // Complexity tradeoff: the chains and the escape solve run on the query's own types
        // only. Why: run on every list type the search meets, they decided or found witnesses
        // for parts the search would have decided its own way, and changed the search's
        // course: 40-60% more work on `r6twowide` and `r6threeun`, which are outside their
        // class, than base 4777a33e, which has neither (R7, Q4). The roots include the types
        // written in a root's tuple and record fields (`fields`): left to the search, a list in
        // a field was refused where the list alone is decided (R8, Q5). Tradeoff: a list type
        // in their class met only as a type the search builds (a narrowed component, a group
        // member) is left to the search.
        if !self.s().roots.contains_key(t) {
            return None;
        }
        if let Some(plan) = self.s().chains.get(t).cloned() {
            return plan;
        }
        self.s().chains.insert(t.clone(), None);
        let plan = match self.find_prefix_chains(t).await {
            Some(plan) => Some(plan),
            None => escape::decide(t),
        };
        self.s().chains.insert(t.clone(), plan.clone());
        plan
    }

    /// A single-pass position sweep over a conjunction of positive and negative rows on a
    /// `link(head, tail)` atom whose tails are either the period-1 carrier cycle `L` or finite
    /// prefix chains ending at `L`.
    // Complexity tradeoff: the general coinductive tuple-box decider (`narrow_tuples`) narrows the
    // tail component by subtracting each active chain's tail (`L & M_{n-1} - F_2 - ... - F_n`),
    // building a fresh intersection/difference type of size `O(k)` at each of `n` unfolding depths
    // and testing all `k` remaining cells against it in `retest`: `Θ(n^2)` work on `front(n)` and
    // `far(n)`. Used: unfold the DAG of prefix chains once (`O(n log n)` via `node_of` and
    // `canon_node` with carrier-relative head normalization), group active depth-`>= 2` chain
    // runs by `(has_stop, head, emit)`, maintain only the active groups and step-indexed jump
    // lists (`active_pos`, `active_neg`, `pos_jumps_at`, `neg_jumps_at`), coalesce partial jumping
    // heads per landing node by De Morgan subtraction, and defer uncovered roots on a single
    // disjoint-hole spine (`clcofront`, `clstaggerholes`) to their depth-1 arrival steps where
    // earliest-deadline prefix matching assigns holes in `O(n log n)`.
    // Tradeoff: when the surviving head slice at a step partially overlaps a group's head without
    // covering its target and outside a single disjoint-hole spine (`had_loose`), the sweep still
    // proves `Empty` soundly if a later step becomes empty, and otherwise returns `None` so the
    // general decider runs unchanged.
    async fn find_prefix_chains(&'m self, t: &Type) -> Option<ChainPlan> {
        let p = t.p();
        if p.bools != 0
            || p.ints.cofinite
            || !p.ints.values.is_empty()
            || p.rats.cofinite
            || !p.rats.values.is_empty()
            || p.floats.cofinite
            || !p.floats.values.is_empty()
            || p.f32s.cofinite
            || !p.f32s.values.is_empty()
            || p.strings.cofinite
            || !p.strings.values.is_empty()
            || p.structs
            || p.morphisms.is_leaf() != Some(false)
            || !p.tuples.is_default()
            || p.atoms.cofinite()
        {
            return None;
        }
        let mut link: Option<(std::sync::Arc<str>, Type)> = None;
        for (name, a) in p.atoms.names() {
            match (a.bare, a.payload == Type::empty()) {
                (true, _) => return None,
                // Not met: the atoms are finite (tested above), so `Atoms::set`, the one writer
                // of `names` (module `types::atoms`), keeps no name whose part is
                // `AtomPart::none()`, neither bare nor with a payload.
                (false, true) => unreachable!("a finite atoms map lists a name with no part"),
                (false, false) => {
                    if link.is_some() {
                        return None;
                    }
                    link = Some((name.clone(), a.payload.clone()));
                }
            }
        }
        let (link_name, payload) = link?;
        let q = payload.p();
        // Named struct payloads are an alternative to positional list pairs, not a list
        // constraint. Ignoring that alternative gives a wrong Empty (R7-C2).
        if q.structs || q.tuples.rest || q.tuples.lens.len() != 1 || !q.tuples.lens.contains_key(&2)
        {
            return None;
        }
        let f = &q.tuples.lens[&2];
        let (taken, refused) = f.forced();
        if taken.is_empty() || refused.is_empty() {
            return None;
        }

        // Find the period-1 carrier cycle among the positive rows or at the base of the positive
        // chains.
        let mut carrier_cycle: Option<Cycle> = None;
        let mut carriers: Vec<Type> = Vec::new();
        let mut has_top_carrier = false;
        {
            let mut s = self.s();
            for a in &taken {
                if let Some(c) = s.cycle(&a[1])
                    && c.period == 1
                    && c.at == 0
                    && c.link == link_name
                    && a[0] == c.item
                {
                    has_top_carrier = true;
                    match &carrier_cycle {
                        None => {
                            carrier_cycle = Some(c);
                            carriers.push(a[1].clone());
                        }
                        // A second carrier of the one cycle is not kept, as in the loop below:
                        // `is_carrier` accepts it by its step, so `walk` maps it to node 0 and
                        // its row is read as one ending at the carrier.
                        Some(prev) if prev == &c => {}
                        Some(_) => return None,
                    }
                }
            }
            if carrier_cycle.is_none() {
                for a in &taken {
                    let mut cur = a[1].clone();
                    let mut vis: TypeSet = TypeSet::with_hasher(Digests::new());
                    while vis.insert(cur.clone()) {
                        if let Some(c) = s.cycle(&cur) {
                            if c.period == 1 && c.at == 0 && c.link == link_name {
                                match &carrier_cycle {
                                    None => {
                                        carrier_cycle = Some(c);
                                        carriers.push(cur);
                                    }
                                    // A second carrier of the one cycle is not kept: its step
                                    // is `(Some(c.stop), c.link, c.item, cur)` (period 1, at
                                    // 0), which `is_carrier` accepts without `carrier_set`, so
                                    // `walk` maps it to node 0 and a row ending there is read as
                                    // one ending at the carrier (TEST-kernel-unreached-paths-4:
                                    // test `chains_to_two_carriers_of_one_cycle_...` reaches this
                                    // arm, and its verdicts were the same with the type kept).
                                    Some(prev) if prev == &c => {}
                                    Some(_) => return None,
                                }
                            }
                            break;
                        }
                        let Some((_, l, _, next)) = list_step(&cur) else {
                            break;
                        };
                        if l != link_name {
                            break;
                        }
                        cur = next;
                    }
                }
            }
        }
        let c = carrier_cycle?;
        let stop_name = c.stop.clone();
        let carrier_head = c.item.clone();

        let mut carrier_set: TypeSet = TypeSet::with_hasher(Digests::new());
        for car in &carriers {
            carrier_set.insert(car.clone());
        }

        let norm_head = |h: &Type| -> Type {
            if *h == carrier_head {
                h.clone()
            } else {
                self.cut(h, &carrier_head, Cut::Meet)
            }
        };

        let is_carrier = |cand: &Type| -> bool {
            if carrier_set.contains(cand) {
                return true;
            }
            let Some((s, l, h, next)) = list_step(cand) else {
                return false;
            };
            s.as_ref() == Some(&stop_name)
                && l == link_name
                && next == *cand
                && norm_head(&h) == carrier_head
        };

        let step_of = |x: &Type| -> Option<(bool, Type, Option<Type>, Type)> {
            if let Some((s, l, h, next)) = list_step(x) {
                if l != link_name || s.as_ref().is_some_and(|st| *st != stop_name) {
                    return None;
                }
                return Some((s.is_some(), norm_head(&h), None, next));
            }
            let xp = x.p();
            if xp.bools != 0
                || xp.ints.cofinite
                || !xp.ints.values.is_empty()
                || xp.rats.cofinite
                || !xp.rats.values.is_empty()
                || xp.floats.cofinite
                || !xp.floats.values.is_empty()
                || xp.f32s.cofinite
                || !xp.f32s.values.is_empty()
                || xp.strings.cofinite
                || !xp.strings.values.is_empty()
                || xp.structs
                || xp.morphisms.is_leaf() != Some(false)
                || !xp.tuples.is_default()
                || xp.atoms.cofinite()
            {
                return None;
            }
            let mut has_stop = false;
            let mut l_payload: Option<Type> = None;
            for (n, a) in xp.atoms.names() {
                match (a.bare, a.payload == Type::empty()) {
                    (true, true) if *n == stop_name => has_stop = true,
                    // Not met: the atoms are finite (tested above), so `Atoms::set`, the one
                    // writer of `names` (module `types::atoms`), keeps no name whose part is
                    // `AtomPart::none()`.
                    (false, true) => unreachable!("a finite atoms map lists a name with no part"),
                    (false, false) if *n == link_name && l_payload.is_none() => {
                        l_payload = Some(a.payload.clone());
                    }
                    _ => return None,
                }
            }
            let Some(l_payload) = l_payload else {
                return has_stop.then(|| (true, Type::empty(), None, carriers[0].clone()));
            };
            let xq = l_payload.p();
            if xq.structs
                || xq.tuples.rest
                || xq.tuples.lens.len() != 1
                || !xq.tuples.lens.contains_key(&2)
            {
                return None;
            }
            let rows = xq.tuples.lens[&2].union_rows()?;
            if rows.len() < 2 {
                return None;
            }
            let mut car_heads: BTreeSet<Type> = BTreeSet::new();
            let mut car_tail: Option<Type> = None;
            let mut chain_row: Option<(Type, Type)> = None;
            for row in rows {
                if is_carrier(&row[1]) {
                    car_heads.insert(norm_head(&row[0]));
                    if car_tail.is_none() {
                        car_tail = Some(row[1].clone());
                    }
                } else if chain_row.is_none() {
                    chain_row = Some((norm_head(&row[0]), row[1].clone()));
                } else {
                    return None;
                }
            }
            // Not met: there are at least two rows and the loop above gives up at a second row
            // that is no carrier, so at least one row is a carrier.
            if car_heads.is_empty() {
                return None;
            }
            let mut car_iter = car_heads.into_iter();
            let first_car = car_iter.next().expect("non-empty");
            let joined_car = car_iter.fold(first_car, |acc, h| self.cut(&acc, &h, Cut::Join));
            match chain_row {
                None => Some((
                    has_stop,
                    joined_car,
                    None,
                    car_tail.expect("car_heads non-empty"),
                )),
                Some((h_next, next)) => Some((has_stop, h_next, Some(joined_car), next)),
            }
        };

        // Check 1 step on every row tail first so a non-chain row alongside a deep chain fails in
        // O(|R|) without walking the deep chain or evaluating the full BDD.
        for a in taken.iter().chain(&refused) {
            if !is_carrier(&a[1]) && step_of(&a[1]).is_none() {
                return None;
            }
        }

        let atoms = f.distinct_atoms();
        if taken.len() + refused.len() != atoms.len() || atoms.is_empty() {
            return None;
        }
        let taken_set: BTreeSet<&Row> = taken.iter().collect();
        if !f.eval(&|a| taken_set.contains(a)) {
            return None;
        }
        // A top carrier row puts the first item in the carrier head. Without one, the carrier
        // only ends the positive chains, and its head being empty bounds nothing before it (R6:
        // `L = nil | cons(E, L)` with `E` empty, `cons(int, cons(int, L)) \ cons(5, L)` holds
        // [0, 0]); the head checks below then decide.
        if has_top_carrier && self.empty(&carrier_head).await {
            return Some(ChainPlan::Empty);
        }

        let mut nodes = vec![ChainNode {
            has_stop: true,
            head: carrier_head.clone(),
            emit: None,
            depth: 0,
            child: 0,
            run: 0,
            jump: None,
        }];
        let mut node_of: ByType<Option<usize>> = ByType::new();
        for car in &carriers {
            node_of.insert(car.clone(), Some(0));
        }
        let mut canon_node: HashMap<(bool, Type, Option<Type>, usize), usize, Digests> =
            HashMap::with_hasher(Digests::new());

        let mut walk = |start: &Type, nodes: &mut Vec<ChainNode>| -> Option<usize> {
            if let Some(&res) = node_of.get(start) {
                return res;
            }
            let mut path: Vec<(Type, bool, Type, Option<Type>)> = Vec::new();
            let mut visiting: TypeSet = TypeSet::with_hasher(Digests::new());
            let mut cur = start.clone();
            let base = loop {
                if let Some(&res) = node_of.get(&cur) {
                    if let Some(idx) = res {
                        break idx;
                    }
                    for (ty, _, _, _) in path {
                        node_of.insert(ty, None);
                    }
                    return None;
                }
                if is_carrier(&cur) {
                    node_of.insert(cur, Some(0));
                    break 0;
                }
                if !visiting.insert(cur.clone()) {
                    node_of.insert(cur, None);
                    for (ty, _, _, _) in path {
                        node_of.insert(ty, None);
                    }
                    return None;
                }
                let Some((has_stop, h, emit, next)) = step_of(&cur) else {
                    node_of.insert(cur, None);
                    for (ty, _, _, _) in path {
                        node_of.insert(ty, None);
                    }
                    return None;
                };
                path.push((cur, has_stop, h, emit));
                cur = next;
            };

            let mut child = base;
            while let Some((ty, has_stop, h, emit)) = path.pop() {
                let d_child = nodes[child].depth;
                let (depth, run, jump) = if d_child == 0 {
                    if emit.is_some() {
                        node_of.insert(ty, None);
                        for (rem, _, _, _) in path {
                            node_of.insert(rem, None);
                        }
                        return None;
                    }
                    (1, 1, None)
                } else if d_child >= 2
                    && nodes[child].has_stop == has_stop
                    && nodes[child].head == h
                    && nodes[child].emit == emit
                {
                    (d_child + 1, nodes[child].run + 1, nodes[child].jump)
                } else {
                    (d_child + 1, 1, Some(child))
                };
                let key = (has_stop, h.clone(), emit.clone(), child);
                let idx = *canon_node.entry(key).or_insert_with(|| {
                    let id = nodes.len();
                    nodes.push(ChainNode {
                        has_stop,
                        head: h,
                        emit,
                        depth,
                        child,
                        run,
                        jump,
                    });
                    id
                });
                node_of.insert(ty, Some(idx));
                child = idx;
            }
            Some(child)
        };

        let mut pos_rows: Vec<(Type, Option<usize>)> = Vec::with_capacity(taken.len());
        for a in &taken {
            let a0 = norm_head(&a[0]);
            if !has_top_carrier && !self.settles(&a[0], &carrier_head, false).await {
                return None;
            }
            if carrier_set.contains(&a[1]) && a0 == carrier_head {
                pos_rows.push((a0, None));
            } else {
                let u = walk(&a[1], &mut nodes)?;
                if nodes[u].depth == 0 {
                    pos_rows.push((a0, None));
                } else {
                    if nodes[u].emit.is_some() {
                        return None;
                    }
                    pos_rows.push((a0, Some(u)));
                }
            }
        }
        // A positive node with a row into the carrier beside its chain row (`emit`) has two
        // continuations, but the positive groups follow the chain row only, so a member through
        // the carrier row would be lost and `Empty` would be wrong (R6: `(cons(int, cons(int,
        // cons(1, L) | cons(2, B))) & L) \ ..` holds [0, 0, 1]). Each node is read once.
        let mut pos_node_seen = vec![false; nodes.len()];
        for (_, idx) in &pos_rows {
            let mut cur = *idx;
            while let Some(u) = cur {
                if u == 0 || pos_node_seen[u] {
                    break;
                }
                pos_node_seen[u] = true;
                if nodes[u].emit.is_some() {
                    return None;
                }
                cur = Some(nodes[u].child);
            }
        }

        // `norm_head` cuts every step head to the carrier head. For a positive step that is exact
        // only when its head lies in the carrier head, or when a top carrier row already bounds
        // the list to carrier elements. Otherwise a value with a non-carrier element further in
        // is lost and `Empty` would be wrong (R5: `the_sweep_agrees_on_random_positive_chains`
        // case 936). Each type reachable from a positive tail is checked once.
        if !has_top_carrier {
            let mut seen: TypeSet = TypeSet::with_hasher(Digests::new());
            let mut todo: Vec<Type> = taken.iter().map(|a| a[1].clone()).collect();
            while let Some(cur) = todo.pop() {
                if carrier_set.contains(&cur) || !seen.insert(cur.clone()) {
                    continue;
                }
                let rows: Vec<(Type, Type)> = if let Some((_, _, h, next)) = list_step(&cur) {
                    vec![(h, next)]
                } else {
                    let xp = cur.p();
                    let link_payload = xp
                        .atoms
                        .names()
                        .iter()
                        .find(|(n, a)| **n == link_name && !a.bare && a.payload != Type::empty())
                        .map(|(_, a)| a.payload.clone());
                    match link_payload {
                        None => Vec::new(),
                        Some(pl) => (pl.p().tuples.lens.get(&2)?.union_rows()?)
                            .into_iter()
                            .map(|r| (r[0].clone(), r[1].clone()))
                            .collect(),
                    }
                };
                for (h, next) in rows {
                    if !self.settles(&h, &carrier_head, false).await {
                        return None;
                    }
                    todo.push(next);
                }
            }
        }

        let mut neg_depth0: BTreeSet<Type> = BTreeSet::new();
        let mut neg_rows_by_head: ByType<Vec<usize>> = ByType::new();
        let mut neg_heads: BTreeSet<Type> = BTreeSet::new();
        for a in &refused {
            let b0 = norm_head(&a[0]);
            let v = walk(&a[1], &mut nodes)?;
            if nodes[v].depth == 0 {
                neg_depth0.insert(b0);
            } else {
                neg_heads.insert(b0.clone());
                neg_rows_by_head.entry(b0).or_default().push(v);
            }
        }

        // Step 1: intersect positive row heads with the carrier head and subtract depth-0 negative
        // row heads in canonical `BTreeSet` order so `r0` is independent of input row order.
        let mut r0 = carrier_head.clone();
        let mut pos1_seen: TypeSet = TypeSet::with_hasher(Digests::new());
        pos1_seen.insert(r0.clone());
        let mut pos1_sorted: BTreeSet<Type> = BTreeSet::new();
        for (a0, _) in &pos_rows {
            if pos1_seen.insert(a0.clone()) {
                pos1_sorted.insert(a0.clone());
            }
        }
        for a0 in &pos1_sorted {
            r0 = self.cut(&r0, a0, Cut::Meet);
        }
        for b0 in &neg_depth0 {
            r0 = self.cut(&r0, b0, Cut::Minus);
        }
        if self.empty(&r0).await {
            return Some(ChainPlan::Empty);
        }

        // Complexity tradeoff: tests can compare the temporal compression with
        // the naive one-link schedule, O(sum of expanded path lengths), while
        // normal calls always keep maximal runs. No input-size switch is used.
        if self.s().expand_chain_runs {
            for node in &mut nodes {
                if node.depth >= 2 {
                    node.run = 1;
                    node.jump = Some(node.child);
                }
            }
        }
        let max_step = 1 + nodes.iter().map(|n| n.depth).max().unwrap_or(0);
        let mut pos_depth1: Vec<Vec<usize>> = vec![Vec::new(); max_step + 2];
        let mut neg_depth1: Vec<Vec<usize>> = vec![Vec::new(); max_step + 2];
        let mut pos_seen_u: Vec<usize> = vec![0; nodes.len()];
        let mut neg_seen_u: Vec<usize> = vec![0; nodes.len()];
        let mut pos_jumps_at: Vec<Vec<(usize, usize)>> = vec![Vec::new(); max_step + 3];
        let mut neg_jumps_at: Vec<Vec<(usize, usize)>> = vec![Vec::new(); max_step + 3];
        let mut covered_neg_at: Vec<Vec<usize>> = vec![Vec::new(); max_step + 3];
        let mut pos_groups: Vec<ChainGroup> = Vec::new();
        let mut active_pos: Vec<usize> = Vec::new();
        let mut pos_group_of: [ByType<usize>; 2] = [ByType::new(), ByType::new()];
        let mut neg_groups: Vec<ChainGroup> = Vec::new();
        let mut active_neg: Vec<usize> = Vec::new();
        let mut neg_group_of: HashMap<(bool, Type, Option<Type>), usize, Digests> =
            HashMap::with_hasher(Digests::new());

        let activate_pos = |u: usize,
                            target_step: usize,
                            nodes: &[ChainNode],
                            pos_seen_u: &mut [usize],
                            pos_depth1: &mut [Vec<usize>],
                            pos_group_of: &mut [ByType<usize>; 2],
                            pos_groups: &mut Vec<ChainGroup>,
                            active_pos: &mut Vec<usize>,
                            pos_jumps_at: &mut [Vec<(usize, usize)>]| {
            if pos_seen_u[u] == target_step {
                return;
            }
            pos_seen_u[u] = target_step;
            if nodes[u].depth == 1 {
                pos_depth1[target_step].push(u);
            } else {
                let s_idx = usize::from(nodes[u].has_stop);
                let g_idx = *pos_group_of[s_idx]
                    .entry(nodes[u].head.clone())
                    .or_insert_with(|| {
                        let id = pos_groups.len();
                        pos_groups.push(ChainGroup {
                            has_stop: nodes[u].has_stop,
                            head: nodes[u].head.clone(),
                            emit: None,
                            active: 0,
                            listed: false,
                            jumping_next: 0,
                            jumping_stop_next: false,
                            jump_target: None,
                            multi_target: false,
                        });
                        id
                    });
                if !pos_groups[g_idx].listed {
                    pos_groups[g_idx].listed = true;
                    active_pos.push(g_idx);
                }
                pos_groups[g_idx].active += 1;
                pos_jumps_at[target_step + nodes[u].run]
                    .push((g_idx, nodes[u].jump.expect("depth >= 2 has jump")));
            }
        };

        let activate_neg =
            |v: usize,
             target_step: usize,
             nodes: &[ChainNode],
             neg_seen_u: &mut [usize],
             neg_depth1: &mut [Vec<usize>],
             neg_group_of: &mut HashMap<(bool, Type, Option<Type>), usize, Digests>,
             neg_groups: &mut Vec<ChainGroup>,
             active_neg: &mut Vec<usize>,
             neg_jumps_at: &mut [Vec<(usize, usize)>]| {
                if neg_seen_u[v] == target_step {
                    return;
                }
                neg_seen_u[v] = target_step;
                if nodes[v].depth == 1 {
                    neg_depth1[target_step].push(v);
                } else {
                    let key = (
                        nodes[v].has_stop,
                        nodes[v].head.clone(),
                        nodes[v].emit.clone(),
                    );
                    let g_idx = *neg_group_of.entry(key).or_insert_with(|| {
                        let id = neg_groups.len();
                        neg_groups.push(ChainGroup {
                            has_stop: nodes[v].has_stop,
                            head: nodes[v].head.clone(),
                            emit: nodes[v].emit.clone(),
                            active: 0,
                            listed: false,
                            jumping_next: 0,
                            jumping_stop_next: false,
                            jump_target: None,
                            multi_target: false,
                        });
                        id
                    });
                    if !neg_groups[g_idx].listed {
                        neg_groups[g_idx].listed = true;
                        active_neg.push(g_idx);
                    }
                    neg_groups[g_idx].active += 1;
                    neg_jumps_at[target_step + nodes[v].run]
                        .push((g_idx, nodes[v].jump.expect("depth >= 2 has jump")));
                }
            };

        for (_, idx) in &pos_rows {
            if let Some(u) = *idx {
                activate_pos(
                    u,
                    2,
                    &nodes,
                    &mut pos_seen_u,
                    &mut pos_depth1,
                    &mut pos_group_of,
                    &mut pos_groups,
                    &mut active_pos,
                    &mut pos_jumps_at,
                );
            }
        }

        let mut had_loose = false;
        let mut non_disjoint_stop_step1: BTreeSet<Type> = BTreeSet::new();
        let mut forced_stop_forbid1 = false;
        let mut target_rem1: HashMap<usize, Option<Type>> = HashMap::new();
        for b0 in &neg_heads {
            let vs = &neg_rows_by_head[b0];
            if pos1_seen.contains(b0) {
                for &v in vs {
                    if nodes[v].has_stop {
                        forced_stop_forbid1 = true;
                    }
                    target_rem1.insert(v, None);
                    activate_neg(
                        v,
                        2,
                        &nodes,
                        &mut neg_seen_u,
                        &mut neg_depth1,
                        &mut neg_group_of,
                        &mut neg_groups,
                        &mut active_neg,
                        &mut neg_jumps_at,
                    );
                }
            }
        }
        for b0 in &neg_heads {
            if pos1_seen.contains(b0) {
                continue;
            }
            let vs = &neg_rows_by_head[b0];
            let forbids_stop = vs.iter().any(|&v| nodes[v].has_stop);
            if !forbids_stop && vs.iter().all(|&v| target_rem1.get(&v) == Some(&None)) {
                continue;
            }
            if self.settles(&r0, b0, false).await {
                if forbids_stop {
                    forced_stop_forbid1 = true;
                }
                for &v in vs {
                    target_rem1.insert(v, None);
                    activate_neg(
                        v,
                        2,
                        &nodes,
                        &mut neg_seen_u,
                        &mut neg_depth1,
                        &mut neg_group_of,
                        &mut neg_groups,
                        &mut active_neg,
                        &mut neg_jumps_at,
                    );
                }
            } else if self.settles(&r0, b0, true).await {
                // Disjoint from `r0`: none of these rows can match at step 1.
            } else {
                if forbids_stop {
                    non_disjoint_stop_step1.insert(b0.clone());
                }
                for &v in vs {
                    let entry = target_rem1.entry(v).or_insert_with(|| Some(r0.clone()));
                    if let Some(rem) = entry {
                        let next_rem = self.cut(rem, b0, Cut::Minus);
                        if self.empty(&next_rem).await {
                            *entry = None;
                        } else {
                            *rem = next_rem;
                        }
                    }
                }
            }
        }
        let mut loose_targets1: Vec<(usize, Type)> = Vec::new();
        for (v, rem_opt) in target_rem1 {
            if let Some(rem) = rem_opt {
                loose_targets1.push((v, rem));
            } else {
                activate_neg(
                    v,
                    2,
                    &nodes,
                    &mut neg_seen_u,
                    &mut neg_depth1,
                    &mut neg_group_of,
                    &mut neg_groups,
                    &mut active_neg,
                    &mut neg_jumps_at,
                );
            }
        }

        // Check whether uncovered step-1 targets `(v, rem)` form a single disjoint-hole spine
        // ending at a depth-1 node `u1` with `has_stop = false` and `emit = None` (`clcofront`,
        // `clstaggerholes`, and staggered single-spine families).
        let mut spine_u1: Option<usize> = None;
        let mut spine_all_holes = true;
        let mut spine_holes: Vec<Option<Type>> = vec![None; max_step + 2];
        let mut spine_arrival: Vec<Option<Type>> = vec![None; max_step + 2];
        // Every value of every spine hole and arrival remainder: a step whose head meets none
        // of them kills no spine root, so passing over it cannot spoil the greedy matching.
        let mut spine_union = Type::empty();
        if !loose_targets1.is_empty() {
            loose_targets1.sort_by_key(|&(v, _)| nodes[v].depth);
            let mut spine_ok = non_disjoint_stop_step1.is_empty()
                && loose_targets1
                    .windows(2)
                    .all(|w| nodes[w[0].0].depth < nodes[w[1].0].depth);
            let mut spine_node_at_depth: Vec<Option<usize>> = vec![None; max_step + 2];
            let mut max_v_depth = 0usize;
            if spine_ok {
                for &(v, _) in &loose_targets1 {
                    max_v_depth = max_v_depth.max(nodes[v].depth);
                    let mut cur = v;
                    while cur != 0 {
                        let d = nodes[cur].depth;
                        if nodes[cur].has_stop || nodes[cur].emit.is_some() {
                            spine_ok = false;
                            break;
                        }
                        if let Some(prev) = spine_node_at_depth[d] {
                            if prev != cur {
                                spine_ok = false;
                            }
                            break;
                        }
                        spine_node_at_depth[d] = Some(cur);
                        cur = nodes[cur].child;
                    }
                    if !spine_ok {
                        break;
                    }
                }
            }
            if spine_ok && let Some(u1) = spine_node_at_depth[1] {
                let mut holes_union = nodes[u1].head.clone();
                for d in 2..=max_v_depth {
                    let w = spine_node_at_depth[d].expect("spine is contiguous");
                    let hole_w = self.cut(&carrier_head, &nodes[w].head, Cut::Minus);
                    if self.empty(&hole_w).await {
                        spine_all_holes = false;
                    } else {
                        if !self.settles(&hole_w, &holes_union, true).await {
                            spine_ok = false;
                            break;
                        }
                        holes_union = self.cut(&holes_union, &hole_w, Cut::Join);
                        spine_holes[d] = Some(hole_w);
                    }
                }
                if spine_ok {
                    for &(v, ref rem) in &loose_targets1 {
                        let t_arr = nodes[v].depth + 1;
                        let covered_by_spine_hole = if let Some(Some(sh)) = spine_holes.get(t_arr) {
                            self.settles(rem, sh, false).await
                        } else {
                            false
                        };
                        if !covered_by_spine_hole {
                            if !self.settles(rem, &holes_union, true).await {
                                spine_ok = false;
                                break;
                            }
                            holes_union = self.cut(&holes_union, rem, Cut::Join);
                        }
                    }
                }
                if spine_ok {
                    spine_u1 = Some(u1);
                    for hole in spine_holes.iter().flatten() {
                        spine_union = self.cut(&spine_union, hole, Cut::Join);
                    }
                    for (v, rem) in loose_targets1 {
                        spine_union = self.cut(&spine_union, &rem, Cut::Join);
                        spine_arrival[nodes[v].depth + 1] = Some(rem);
                    }
                } else {
                    had_loose = true;
                }
            } else {
                had_loose = true;
            }
        }

        // Check whether a 1-element list `link(v0, stop)` already satisfies `t`.
        let pos_allows_stop1 = pos_rows
            .iter()
            .all(|(_, idx)| idx.is_none_or(|u| nodes[u].has_stop));
        if pos_allows_stop1 && !forced_stop_forbid1 {
            if non_disjoint_stop_step1.is_empty() {
                return Some(ChainPlan::Inhabited {
                    stop: stop_name,
                    link: link_name,
                    heads: vec![r0],
                    hints: Vec::new(),
                });
            }
            let mut w0 = r0.clone();
            for b0 in &non_disjoint_stop_step1 {
                w0 = self.cut(&w0, b0, Cut::Minus);
            }
            if !self.empty(&w0).await {
                return Some(ChainPlan::Inhabited {
                    stop: stop_name,
                    link: link_name,
                    heads: vec![w0],
                    hints: Vec::new(),
                });
            }
        }
        if had_loose
            && active_pos.is_empty()
            && pos_depth1[2].is_empty()
            && neg_depth1[2].is_empty()
            && active_neg
                .iter()
                .all(|&g| neg_groups[g].has_stop && neg_groups[g].emit.is_none())
        {
            return None;
        }

        let mut witness_heads = vec![r0];
        let mut step_exact = vec![false; max_step + 2];
        step_exact[1] = !had_loose && non_disjoint_stop_step1.is_empty();
        let mut committed_step = vec![false; max_step + 2];
        let mut committed_count = 0usize;
        let mut next_uncommitted_s = 2usize;
        // Set when a root's scan passes over a free step that meets some hole but cannot take
        // this root. Giving each forced root the earliest free step that kills it is a maximum
        // matching only while the steps each root can use grow with its arrival; a pass-over
        // like this can break that (R5 `r5greedy`: [4, 2, 1, 1] escapes, yet the greedy gives
        // step 1 to the earlier root), so `Empty` is then left to the search.
        let mut greedy_unsafe = false;
        // Complexity tradeoff: exploring both optional spine branches requires potentially
        // exponential search. Keep the O(1) witness choice, but never use its exhaustion
        // as an Empty proof for the original type (X31). One Boolean, no size cutoff.
        let mut optional_spine_choice = false;

        for step in 2..=max_step + 1 {
            let pos_jumps = std::mem::take(&mut pos_jumps_at[step]);
            let mut pos_to_activate: Vec<usize> = Vec::with_capacity(pos_jumps.len());
            for (g_idx, u) in pos_jumps {
                if pos_groups[g_idx].active > 0 {
                    pos_groups[g_idx].active -= 1;
                    pos_to_activate.push(u);
                }
            }
            for u in pos_to_activate {
                activate_pos(
                    u,
                    step,
                    &nodes,
                    &mut pos_seen_u,
                    &mut pos_depth1,
                    &mut pos_group_of,
                    &mut pos_groups,
                    &mut active_pos,
                    &mut pos_jumps_at,
                );
            }
            // Complexity tradeoff: an exhausted group can be re-entered by another
            // group's jump before this retain. Testing active == 0 when inserting
            // appended its index again, giving Theta(n²) visits on two alternating
            // chains of O(n) nodes. A listed bit makes the vector a set: O(1) per
            // insertion/removal, one flag per group; token counts remain unchanged.
            active_pos.retain(|&g_idx| {
                pos_groups[g_idx].listed = pos_groups[g_idx].active > 0;
                pos_groups[g_idx].listed
            });

            let neg_jumps = std::mem::take(&mut neg_jumps_at[step]);
            let mut neg_to_activate: Vec<usize> = Vec::with_capacity(neg_jumps.len());
            for (g_idx, u) in neg_jumps {
                if neg_groups[g_idx].active > 0 {
                    neg_groups[g_idx].active -= 1;
                    neg_to_activate.push(u);
                }
            }
            let cov_neg = std::mem::take(&mut covered_neg_at[step]);
            neg_to_activate.extend(cov_neg);
            for w in neg_to_activate {
                activate_neg(
                    w,
                    step,
                    &nodes,
                    &mut neg_seen_u,
                    &mut neg_depth1,
                    &mut neg_group_of,
                    &mut neg_groups,
                    &mut active_neg,
                    &mut neg_jumps_at,
                );
            }
            // Complexity tradeoff: as for active_pos, retain one entry per live
            // generation even when a jump re-enters an exhausted group this step.
            active_neg.retain(|&g_idx| {
                neg_groups[g_idx].listed = neg_groups[g_idx].active > 0;
                neg_groups[g_idx].listed
            });

            let pos_stop_now = pos_depth1[step].iter().all(|&u| nodes[u].has_stop)
                && active_pos.iter().all(|&g_idx| pos_groups[g_idx].has_stop);
            let neg_stop_now = neg_depth1[step].iter().any(|&u| nodes[u].has_stop)
                || active_neg.iter().any(|&g_idx| neg_groups[g_idx].has_stop);
            if pos_stop_now && !neg_stop_now {
                return (!had_loose).then_some(ChainPlan::Inhabited {
                    stop: stop_name,
                    link: link_name,
                    heads: witness_heads,
                    hints: Vec::new(),
                });
            }
            if step > max_step {
                return None;
            }

            let mut r0 = carrier_head.clone();
            let mut pos_seen: TypeSet = TypeSet::with_hasher(Digests::new());
            pos_seen.insert(r0.clone());
            let mut pos_step_sorted: BTreeSet<Type> = BTreeSet::new();
            for &u in &pos_depth1[step] {
                if pos_seen.insert(nodes[u].head.clone()) {
                    pos_step_sorted.insert(nodes[u].head.clone());
                }
            }
            for &g_idx in &active_pos {
                let pg = &pos_groups[g_idx];
                if pos_seen.insert(pg.head.clone()) {
                    pos_step_sorted.insert(pg.head.clone());
                }
            }
            for h in &pos_step_sorted {
                r0 = self.cut(&r0, h, Cut::Meet);
            }
            let mut neg_seen: TypeSet = TypeSet::with_hasher(Digests::new());
            let mut neg_step_sorted: BTreeSet<Type> = BTreeSet::new();
            for &u in &neg_depth1[step] {
                if neg_seen.insert(nodes[u].head.clone()) {
                    neg_step_sorted.insert(nodes[u].head.clone());
                }
            }
            for &g_idx in &active_neg {
                if let Some(ref h_emit) = neg_groups[g_idx].emit
                    && neg_seen.insert(h_emit.clone())
                {
                    neg_step_sorted.insert(h_emit.clone());
                }
            }
            for h in &neg_step_sorted {
                r0 = self.cut(&r0, h, Cut::Minus);
            }
            if self.empty(&r0).await {
                return (!greedy_unsafe
                    && !optional_spine_choice
                    && (committed_count == 0 || (spine_all_holes && !had_loose)))
                    .then_some(ChainPlan::Empty);
            }

            for &(g_idx, u) in &neg_jumps_at[step + 1] {
                let ng = &mut neg_groups[g_idx];
                if ng.active > 0 {
                    ng.jumping_next += 1;
                    ng.jumping_stop_next |= nodes[u].has_stop;
                    if ng.jumping_next == 1 {
                        ng.jump_target = Some(u);
                        ng.multi_target = false;
                    } else if ng.jump_target != Some(u) {
                        ng.multi_target = true;
                    }
                }
            }

            // If a deferred disjoint-hole spine root arrives at its depth-1 leaf `u1` at `step`,
            // decide whether to kill it at an uncommitted earlier step `s < step` or subtract
            // `nodes[u1].head` from `r0` at `step`.
            if let (Some(u1), Some(rem1)) = (spine_u1, spine_arrival[step].clone()) {
                let h1 = &nodes[u1].head;
                let r0_without_h1 = self.cut(&r0, h1, Cut::Minus);
                let spine_union = &spine_union;
                let try_kill = async |witness_heads: &mut [Type],
                                      committed_step: &mut [bool],
                                      committed_count: &mut usize,
                                      next_uncommitted_s: &mut usize,
                                      greedy_unsafe: &mut bool|
                       -> bool {
                    // A free step passed over: unsafe unless its head meets no hole at all.
                    let passed = async |head: &Type| {
                        !self.empty(&self.cut(head, spine_union, Cut::Meet)).await
                    };
                    if !committed_step[1] {
                        if step_exact[1] {
                            let cand1 = self.cut(&witness_heads[0], &rem1, Cut::Meet);
                            if !self.empty(&cand1).await {
                                witness_heads[0] = cand1;
                                committed_step[1] = true;
                                *committed_count += 1;
                                return true;
                            }
                        }
                        *greedy_unsafe |= passed(&witness_heads[0]).await;
                    }
                    let start_s = if spine_all_holes {
                        *next_uncommitted_s
                    } else {
                        2
                    };
                    for s in start_s..step {
                        if committed_step[s] || !step_exact[s] {
                            if spine_all_holes && s == *next_uncommitted_s {
                                *next_uncommitted_s = s + 1;
                            }
                            if !committed_step[s] && !*greedy_unsafe {
                                *greedy_unsafe = passed(&witness_heads[s - 1]).await;
                            }
                            continue;
                        }
                        if let Some(ref h_hole) = spine_holes[step + 1 - s] {
                            let cand = self.cut(&witness_heads[s - 1], h_hole, Cut::Meet);
                            if !self.empty(&cand).await {
                                witness_heads[s - 1] = cand;
                                committed_step[s] = true;
                                *committed_count += 1;
                                if spine_all_holes && s == *next_uncommitted_s {
                                    *next_uncommitted_s = s + 1;
                                }
                                return true;
                            }
                        }
                        if !*greedy_unsafe {
                            *greedy_unsafe = passed(&witness_heads[s - 1]).await;
                        }
                    }
                    false
                };

                if self.empty(&r0_without_h1).await {
                    if !try_kill(
                        &mut witness_heads,
                        &mut committed_step,
                        &mut committed_count,
                        &mut next_uncommitted_s,
                        &mut greedy_unsafe,
                    )
                    .await
                    {
                        return (!greedy_unsafe
                            && !optional_spine_choice
                            && (committed_count == 0 || (spine_all_holes && !had_loose)))
                            .then_some(ChainPlan::Empty);
                    }
                } else {
                    // Check whether keeping `h1` allows stopping right after `step`.
                    let mut pos_allows_stop_next = true;
                    for &(g_idx, u) in &pos_jumps_at[step + 1] {
                        let pg = &mut pos_groups[g_idx];
                        if pg.active > 0 {
                            pg.jumping_next += 1;
                            pg.jumping_stop_next |= !nodes[u].has_stop;
                        }
                    }
                    for &g_idx in &active_pos {
                        let pg = &mut pos_groups[g_idx];
                        let staying = pg.active - pg.jumping_next;
                        let ok = (staying == 0 || pg.has_stop) && !pg.jumping_stop_next;
                        pg.jumping_next = 0;
                        pg.jumping_stop_next = false;
                        pos_allows_stop_next &= ok;
                    }
                    if !had_loose && pos_allows_stop_next {
                        let mut stop_forbid_heads: BTreeSet<Type> = BTreeSet::new();
                        for &g_idx in &active_neg {
                            let ng = &neg_groups[g_idx];
                            let staying = ng.active - ng.jumping_next;
                            if (staying > 0 && ng.has_stop) || ng.jumping_stop_next {
                                stop_forbid_heads.insert(ng.head.clone());
                            }
                        }
                        let mut w0_full = r0.clone();
                        for h in &stop_forbid_heads {
                            w0_full = self.cut(&w0_full, h, Cut::Minus);
                        }
                        if !self.empty(&w0_full).await {
                            let w0_no_h1 = self.cut(&w0_full, h1, Cut::Minus);
                            if !self.empty(&w0_no_h1).await {
                                witness_heads.push(w0_no_h1);
                                return Some(ChainPlan::Inhabited {
                                    stop: stop_name,
                                    link: link_name,
                                    heads: witness_heads,
                                    hints: Vec::new(),
                                });
                            }
                            if try_kill(
                                &mut witness_heads,
                                &mut committed_step,
                                &mut committed_count,
                                &mut next_uncommitted_s,
                                &mut greedy_unsafe,
                            )
                            .await
                            {
                                witness_heads.push(w0_full);
                                return Some(ChainPlan::Inhabited {
                                    stop: stop_name,
                                    link: link_name,
                                    heads: witness_heads,
                                    hints: Vec::new(),
                                });
                            }
                        }
                    }
                    // With no active negative chain, the two passes below read nothing of `r0`, the
                    // later reads of `r0` at this step only build a witness, and every later
                    // hole is disjoint from `h1`; so no chain can tell the narrowing apart and
                    // it stays an `Empty` proof (Gemini R7 Q2(a)).
                    if !active_neg.is_empty() {
                        optional_spine_choice = true;
                    }
                    r0 = r0_without_h1;
                }
            }

            let mut non_disjoint_stop_heads: BTreeSet<Type> = BTreeSet::new();
            let mut forced_stop_forbid = false;
            let mut step_loose = false;
            let mut target_rem: HashMap<usize, Option<Type>> = HashMap::new();
            let mut multi_partial_groups: HashSet<usize> = HashSet::new();

            // Pass 1: active negative groups whose head is already guaranteed to hold on `r0`.
            for &g_idx in &active_neg {
                let ng = &mut neg_groups[g_idx];
                if !pos_seen.contains(&ng.head) {
                    continue;
                }
                let staying = ng.active - ng.jumping_next;
                let forbids_stop_next = (staying > 0 && ng.has_stop) || ng.jumping_stop_next;
                ng.jumping_next = 0;
                ng.jumping_stop_next = false;
                if forbids_stop_next {
                    forced_stop_forbid = true;
                }
                if !ng.multi_target
                    && let Some(w) = ng.jump_target.take()
                {
                    target_rem.insert(w, None);
                }
            }
            for &(g_idx, w) in &neg_jumps_at[step + 1] {
                if neg_groups[g_idx].active > 0 && pos_seen.contains(&neg_groups[g_idx].head) {
                    target_rem.insert(w, None);
                }
            }

            // A group key is (has_stop, head, emit), not a landing node. Each
            // scheduled token keeps its own child. Pass 1 forces each such child;
            // Pass 2 unions only the partial heads actually landing at that child.
            // Pass 2: remaining active negative groups, coalescing partial jumps per landing node.
            for &g_idx in &active_neg {
                if pos_seen.contains(&neg_groups[g_idx].head) {
                    continue;
                }
                let ng = &mut neg_groups[g_idx];
                let staying = ng.active - ng.jumping_next;
                let jumping_next = ng.jumping_next;
                let forbids_stop_next = (staying > 0 && ng.has_stop) || ng.jumping_stop_next;
                let jump_target = ng.jump_target.take();
                let multi_target = ng.multi_target;
                ng.jumping_next = 0;
                ng.jumping_stop_next = false;
                ng.multi_target = false;

                if staying == 0
                    && !forbids_stop_next
                    && !multi_target
                    && jump_target.is_some_and(|w| target_rem.get(&w) == Some(&None))
                {
                    // A killed group leaves its scheduled jumps in `neg_jumps_at`. Dropping its
                    // key makes a later token with the same key start a new group, so the stale
                    // jumps meet `active == 0` and are ignored instead of counting against that
                    // token (R5: `r5_sat_check` at k = 4, m = 3 overflowed `staying`).
                    ng.active = 0;
                    neg_group_of.remove(&(ng.has_stop, ng.head.clone(), ng.emit.clone()));
                    continue;
                }

                if self.settles(&r0, &ng.head, false).await {
                    if forbids_stop_next {
                        forced_stop_forbid = true;
                    }
                    if !multi_target && let Some(w) = jump_target {
                        target_rem.insert(w, None);
                    }
                } else if self.settles(&r0, &ng.head, true).await {
                    ng.active = 0;
                    neg_group_of.remove(&(ng.has_stop, ng.head.clone(), ng.emit.clone()));
                } else {
                    if forbids_stop_next {
                        non_disjoint_stop_heads.insert(ng.head.clone());
                    }
                    if staying > 0 || jumping_next == 0 {
                        step_loose = true;
                    } else if !multi_target && let Some(w) = jump_target {
                        let entry = target_rem.entry(w).or_insert_with(|| Some(r0.clone()));
                        if let Some(rem) = entry {
                            let next_rem = self.cut(rem, &ng.head, Cut::Minus);
                            if self.empty(&next_rem).await {
                                *entry = None;
                            } else {
                                *rem = next_rem;
                            }
                        }
                    } else {
                        multi_partial_groups.insert(g_idx);
                    }
                    ng.active = 0;
                    neg_group_of.remove(&(ng.has_stop, ng.head.clone(), ng.emit.clone()));
                }
            }

            if !multi_partial_groups.is_empty() {
                for &(g_idx, w) in &neg_jumps_at[step + 1] {
                    if multi_partial_groups.contains(&g_idx) {
                        let h = &neg_groups[g_idx].head;
                        let entry = target_rem.entry(w).or_insert_with(|| Some(r0.clone()));
                        if let Some(rem) = entry {
                            let next_rem = self.cut(rem, h, Cut::Minus);
                            if self.empty(&next_rem).await {
                                *entry = None;
                            } else {
                                *rem = next_rem;
                            }
                        }
                    }
                }
            }

            let mut rem_cuts: BTreeSet<Type> = BTreeSet::new();
            for (w, rem_opt) in target_rem {
                if let Some(rem) = rem_opt {
                    rem_cuts.insert(rem);
                } else {
                    covered_neg_at[step + 1].push(w);
                }
            }
            // Dominance at a fully jumping partial transition: for each child w,
            // its rem is R minus the union of heads whose tokens land at w.
            // None means that union covers R (or a forced token reaches w).
            // If their intersection is nonempty, choosing x there kills all
            // partial children simultaneously. Every other x retains at least
            // the forced children. Positive obligations are uniform on R; with
            // no partial stopping head and no deferred spine, replacing x this
            // way cannot destroy a solution. Staying partial tokens are dropped
            // only with step_loose, so this dominance is not asserted for them.
            //
            // Why `!step_loose` changes only precision, never a verdict (U7 of REFUSAL-front-
            // unsolved; the Q4 argument of Codex R11, read again by front1). Drop `!step_loose`:
            // the narrowing then also runs on a step already loose, and only `r0` differs. (1)
            // `step_loose` stays true either way, so `had_loose` and `step_exact[step]` are the
            // same after this step. (2) Every later step rebuilds `r0` from `carrier_head`; the
            // `Empty` returns read `greedy_unsafe`, `optional_spine_choice`, `committed_count`,
            // `spine_all_holes` and `had_loose`, none of which reads this `r0`; `try_kill`, the one
            // reader of earlier `witness_heads`, runs only when `spine_u1` is `Some`, which the
            // guard excludes and which is fixed before the loop. (3) Every later `Inhabited`
            // return needs `!had_loose`, now false. (4) The return below at this step reads `r0`
            // only as the witness: the narrowing needs `non_disjoint_stop_heads` empty, so it
            // takes the branch that pushes `r0` (nonempty either way), and `chain_rep` checks
            // that witness from scratch, falling back to the search when it fails. So the
            // mutant can change the witness shown, or turn a checked answer into the search's,
            // but it cannot add an `Empty`. The other two conjuncts carry the dominance argument
            // above (Codex R11 Q4); this paragraph does not cover them.
            if !rem_cuts.is_empty() {
                if !step_loose && non_disjoint_stop_heads.is_empty() && spine_u1.is_none() {
                    let mut r0_narrow = r0.clone();
                    for rem in &rem_cuts {
                        r0_narrow = self.cut(&r0_narrow, rem, Cut::Meet);
                    }
                    if !self.empty(&r0_narrow).await {
                        r0 = r0_narrow;
                    } else {
                        step_loose = true;
                    }
                } else {
                    step_loose = true;
                }
            }

            if !had_loose && !forced_stop_forbid {
                for &(g_idx, u) in &pos_jumps_at[step + 1] {
                    let pg = &mut pos_groups[g_idx];
                    if pg.active > 0 {
                        pg.jumping_next += 1;
                        pg.jumping_stop_next |= !nodes[u].has_stop;
                    }
                }
                let mut pos_allows_stop_next = true;
                for &g_idx in &active_pos {
                    let pg = &mut pos_groups[g_idx];
                    let staying = pg.active - pg.jumping_next;
                    let ok = (staying == 0 || pg.has_stop) && !pg.jumping_stop_next;
                    pg.jumping_next = 0;
                    pg.jumping_stop_next = false;
                    pos_allows_stop_next &= ok;
                }
                if pos_allows_stop_next {
                    if non_disjoint_stop_heads.is_empty() {
                        witness_heads.push(r0);
                        return Some(ChainPlan::Inhabited {
                            stop: stop_name,
                            link: link_name,
                            heads: witness_heads,
                            hints: Vec::new(),
                        });
                    }
                    let mut w0 = r0.clone();
                    for h in &non_disjoint_stop_heads {
                        w0 = self.cut(&w0, h, Cut::Minus);
                    }
                    if !self.empty(&w0).await {
                        witness_heads.push(w0);
                        return Some(ChainPlan::Inhabited {
                            stop: stop_name,
                            link: link_name,
                            heads: witness_heads,
                            hints: Vec::new(),
                        });
                    }
                }
            }

            had_loose |= step_loose;
            step_exact[step] = !step_loose && non_disjoint_stop_heads.is_empty();
            witness_heads.push(r0);
        }

        None
    }

    /// Builds and independently verifies the witness list of a [`ChainPlan::Inhabited`] plan.
    /// The witness is checked against `t` from scratch by [`Searching::check_chain_witness`]
    /// before it is shown or recorded in `Search::members` and `Search::reps`; if verification
    /// fails, returns `None`.
    async fn chain_rep(&'m self, t: &Type, plan: ChainPlan) -> Option<usize> {
        if let Some(Some(r)) = self.s().reps.get(t).copied() {
            return Some(r);
        }
        let ChainPlan::Inhabited {
            stop,
            link,
            heads,
            hints,
        } = plan
        else {
            return None;
        };
        let (seeding, walking, current) = {
            let mut s = self.s();
            (
                std::mem::replace(&mut s.seeding, false),
                std::mem::replace(&mut s.walking, false),
                s.current.take(),
            )
        };
        let mut head_reps: ByType<usize> = ByType::new();
        let mut items: Vec<usize> = Vec::with_capacity(heads.len());
        for h in &heads {
            if let Some(&r) = head_reps.get(h) {
                items.push(r);
            } else {
                let Some(r) = self.rep(h).await else {
                    let mut s = self.s();
                    s.seeding = seeding;
                    s.walking = walking;
                    s.current = current;
                    return None;
                };
                head_reps.insert(h.clone(), r);
                items.push(r);
            }
        }
        let verified = self
            .check_chain_witness(t, &link, &items, &stop, &hints)
            .await;
        {
            let mut s = self.s();
            s.seeding = seeding;
            s.walking = walking;
            s.current = current;
        }
        if !verified {
            return None;
        }
        let mut cur = self.s().show(Rep::Value(Value::atom(&stop)));
        for &item in items.iter().rev() {
            let tup = self.s().show(Rep::Tuple(vec![item, cur]));
            cur = self.s().show(Rep::Atom(link.clone(), tup));
        }
        let mut s = self.s();
        let c = s.class(cur);
        s.members.insert((c, t.clone()), Some(true));
        s.reps.insert(t.clone(), Some(cur));
        Some(cur)
    }

    /// Independently checks that the list with item representatives `items` (from front to back)
    /// linked by `link` and ending in `stop` belongs to `t`, without reading `ChainPlan`,
    /// `ChainNode` or `ChainGroup`. Each row of `t`'s link payload is evaluated by unfolding its
    /// tail graph from scratch, normalizing heads against the carrier head once all witness items
    /// are checked against it, compressing acyclic runs of identical `(has_stop, head, emit)`
    /// steps, and jumping across constant-item witness runs along non-uniform chains with
    /// memoized pass lengths and binary lifting.
    // Complexity tradeoff: checking a length-`O(n)` list witness against `n` chain rows by walking
    // the witness step-by-step per row (`Searching::holds` / `member_known`) takes `O(k)` steps on
    // row `F_k` and `Θ(n^2)` in total; preallocating a length-`n` table for every distinct head
    // type also takes `Θ(n^2)` when `n` rows have `n` distinct head types (`groupsfar`,
    // `manyheadsfar`, `clmanyheadsfar`). Used: verify all witness items against the carrier head
    // first so heads differing only outside the carrier (`clstaggerfar`) normalize to one head;
    // compress acyclic runs of identical `(has_stop, head, emit)` nodes into `(run, jump)`;
    // precompute maximal runs of identical witness item IDs (`run_end` and `run_start`) in `O(m)`;
    // and on non-uniform chains (`clstaggerholes`), memoize `pass_memo[(node, item)]` along the
    // chain and jump `O(n)` links in `O(log n)` via binary-lifting pointers `up: [usize; 18]`.
    // Total work across all rows is `O(n log n)`.
    #[allow(clippy::type_complexity)]
    async fn check_chain_witness(
        &'m self,
        t: &Type,
        link: &std::sync::Arc<str>,
        items: &[usize],
        stop: &std::sync::Arc<str>,
        hints: &[(Row, ChainHint)],
    ) -> bool {
        if items.is_empty() {
            let p = t.p();
            return p
                .atoms
                .names()
                .get(stop)
                .map_or(p.atoms.cofinite(), |a| a.bare);
        }
        let p = t.p();
        let Some(a) = p.atoms.names().get(link) else {
            return p.atoms.cofinite();
        };
        let q = a.payload.p();
        let Some(f) = q.tuples.lens.get(&2) else {
            return q.tuples.rest;
        };
        let atoms = f.distinct_atoms();
        if items.len() == 1 {
            let mut known: BTreeMap<Row, Option<bool>> = BTreeMap::new();
            for row in atoms {
                let head0 = self.member_known(items[0], &row[0]).await;
                let fits = match head0 {
                    Some(false) => Some(false),
                    other => {
                        let rp = row[1].p();
                        let tail_ok = rp
                            .atoms
                            .names()
                            .get(stop)
                            .map_or(rp.atoms.cofinite(), |x| x.bare);
                        if tail_ok { other } else { Some(false) }
                    }
                };
                known.insert(row, fits);
            }
            return f.eval3(&|row| known.get(row).copied().flatten()) == Some(true);
        }

        // If `t` has a self-looping carrier cycle `L = stop | link(c_head, L)` and every witness
        // item belongs to `c_head`, any head `h` tested on witness items agrees with `h & c_head`.
        let mut verified_carrier: Option<Type> = None;
        {
            let (taken, _) = f.forced();
            let mut cand_head: Option<Type> = None;
            for row in &taken {
                if let Some((s, l, h, next)) = list_step(&row[1])
                    && s.as_ref() == Some(stop)
                    && l == *link
                    && next == row[1]
                    && row[0] == h
                {
                    cand_head = Some(h);
                    break;
                }
            }
            if cand_head.is_none()
                && let Some(row) = taken.first()
            {
                let mut cur = row[1].clone();
                let mut vis: TypeSet = TypeSet::with_hasher(Digests::new());
                while vis.insert(cur.clone()) {
                    let Some((s, l, h, next)) = list_step(&cur) else {
                        break;
                    };
                    if l != *link {
                        break;
                    }
                    if s.as_ref() == Some(stop) && next == cur {
                        cand_head = Some(h);
                        break;
                    }
                    cur = next;
                }
            }
            if let Some(ch) = cand_head {
                let mut all_in_ch = true;
                let mut checked_items: HashSet<usize> = HashSet::new();
                for &item in items {
                    if checked_items.insert(item)
                        && self.member_known(item, &ch).await != Some(true)
                    {
                        all_in_ch = false;
                        break;
                    }
                }
                if all_in_ch {
                    verified_carrier = Some(ch);
                }
            }
        }

        struct VerifyNode {
            has_stop: bool,
            head: usize,
            emit: Option<(usize, usize)>,
            next: usize,
            on_cycle: bool,
            run: usize,
            jump: usize,
            up: [usize; 18],
            /// Links to the first node on a cycle (0 on a cycle).
            acyc: usize,
            /// Nodes with an `emit` from this one to the first on a cycle, both counted.
            emits: usize,
        }

        let mut heads: Vec<Type> = Vec::new();
        let mut head_ids: ByType<usize> = ByType::new();
        let mut intern_head = |ty: &Type| -> usize {
            let norm = match &verified_carrier {
                Some(ch) if *ty != *ch => self.cut(ty, ch, Cut::Meet),
                _ => ty.clone(),
            };
            if let Some(&id) = head_ids.get(&norm) {
                return id;
            }
            let id = heads.len();
            heads.push(norm.clone());
            head_ids.insert(norm, id);
            id
        };

        let verify_step = |x: &Type,
                           intern_head: &mut dyn FnMut(&Type) -> usize|
         -> Option<(bool, usize, Option<(usize, usize)>, Type)> {
            if let Some((s, l, h, next)) = list_step(x) {
                if l != *link || s.as_ref().is_some_and(|st| st != stop) {
                    return None;
                }
                return Some((s.is_some(), intern_head(&h), None, next));
            }
            let xp = x.p();
            if xp.bools != 0
                || xp.ints.cofinite
                || !xp.ints.values.is_empty()
                || xp.rats.cofinite
                || !xp.rats.values.is_empty()
                || xp.floats.cofinite
                || !xp.floats.values.is_empty()
                || xp.f32s.cofinite
                || !xp.f32s.values.is_empty()
                || xp.strings.cofinite
                || !xp.strings.values.is_empty()
                || xp.structs
                || xp.morphisms.is_leaf() != Some(false)
                || !xp.tuples.is_default()
                || xp.atoms.cofinite()
            {
                return None;
            }
            let mut has_stop = false;
            let mut l_payload: Option<Type> = None;
            for (n, at) in xp.atoms.names() {
                match (at.bare, at.payload == Type::empty()) {
                    (true, true) if n == stop => has_stop = true,
                    // Never met: the atoms are finite (tested above), and `Atoms::set`, the one
                    // writer of `names` (module `types::atoms`), keeps no name whose part is
                    // `AtomPart::none()` there.
                    (false, true) => unreachable!("a finite atoms map lists a name with no part"),
                    (false, false) if n == link && l_payload.is_none() => {
                        l_payload = Some(at.payload.clone());
                    }
                    _ => return None,
                }
            }
            let Some(l_payload) = l_payload else {
                return has_stop.then(|| (true, intern_head(&Type::empty()), None, x.clone()));
            };
            let xq = l_payload.p();
            if xq.tuples.rest || xq.tuples.lens.len() != 1 || !xq.tuples.lens.contains_key(&2) {
                return None;
            }
            let rows = xq.tuples.lens[&2].union_rows()?;
            if rows.len() < 2 {
                return None;
            }
            let self_loop = |cand: &Type| -> Option<Type> {
                let (s, l, h_loop, next) = list_step(cand)?;
                (s.as_ref() == Some(stop) && l == *link && next == *cand).then_some(h_loop)
            };
            let mut loop_heads: BTreeSet<Type> = BTreeSet::new();
            let mut loop_item: Option<Type> = None;
            let mut loop_tail: Option<Type> = None;
            let mut chain_row: Option<(Type, Type)> = None;
            for row in rows {
                if let Some(h_loop) = self_loop(&row[1]) {
                    if let Some(ref prev_loop) = loop_item
                        && *prev_loop != h_loop
                    {
                        return None;
                    }
                    loop_item = Some(h_loop);
                    loop_heads.insert(row[0].clone());
                    if loop_tail.is_none() {
                        loop_tail = Some(row[1].clone());
                    }
                } else if chain_row.is_none() {
                    chain_row = Some((row[0].clone(), row[1].clone()));
                } else {
                    return None;
                }
            }
            if loop_heads.is_empty() {
                return None;
            }
            let mut loop_iter = loop_heads.into_iter();
            let first_loop = loop_iter.next().expect("non-empty");
            let joined_loop = loop_iter.fold(first_loop, |acc, h| self.cut(&acc, &h, Cut::Join));
            match chain_row {
                None => Some((
                    has_stop,
                    intern_head(&joined_loop),
                    None,
                    loop_tail.expect("non-empty"),
                )),
                Some((h_next, next)) => {
                    let emit = (
                        intern_head(&joined_loop),
                        intern_head(&loop_item.expect("non-empty")),
                    );
                    Some((has_stop, intern_head(&h_next), Some(emit), next))
                }
            }
        };

        let mut nodes: Vec<VerifyNode> = Vec::new();
        let mut node_of: ByType<Option<usize>> = ByType::new();
        let mut canon_verify: HashMap<(bool, usize, Option<(usize, usize)>, usize), usize> =
            HashMap::new();

        let mut unfold = |start: &Type,
                          intern_head: &mut dyn FnMut(&Type) -> usize|
         -> Option<usize> {
            if let Some(&res) = node_of.get(start) {
                return res;
            }
            let mut path: Vec<(Type, bool, usize, Option<(usize, usize)>)> = Vec::new();
            let mut seen_on_path: ByType<usize> = ByType::new();
            let mut cur = start.clone();
            let mut child = loop {
                if let Some(&res) = node_of.get(&cur) {
                    if let Some(idx) = res {
                        break idx;
                    }
                    for (ty, _, _, _) in path {
                        node_of.insert(ty, None);
                    }
                    return None;
                }
                if let Some(&cyc_start) = seen_on_path.get(&cur) {
                    let cyc_len = path.len() - cyc_start;
                    let base_id = nodes.len();
                    for (offset, (ty, has_stop, head, emit)) in path.drain(cyc_start..).enumerate()
                    {
                        let next_id = base_id + (offset + 1) % cyc_len;
                        let id = nodes.len();
                        nodes.push(VerifyNode {
                            has_stop,
                            head,
                            emit,
                            next: next_id,
                            on_cycle: true,
                            run: 1,
                            jump: next_id,
                            up: [id; 18],
                            acyc: 0,
                            emits: usize::from(emit.is_some()),
                        });
                        node_of.insert(ty, Some(id));
                    }
                    break base_id;
                }
                let Some((has_stop, head, emit, next)) = verify_step(&cur, intern_head) else {
                    node_of.insert(cur, None);
                    for (ty, _, _, _) in path {
                        node_of.insert(ty, None);
                    }
                    return None;
                };
                seen_on_path.insert(cur.clone(), path.len());
                path.push((cur, has_stop, head, emit));
                cur = next;
            };

            while let Some((ty, has_stop, head, emit)) = path.pop() {
                let (run, jump) = if !nodes[child].on_cycle
                    && nodes[child].has_stop == has_stop
                    && nodes[child].head == head
                    && nodes[child].emit == emit
                {
                    (1 + nodes[child].run, nodes[child].jump)
                } else {
                    (1, child)
                };
                let id = *canon_verify
                    .entry((has_stop, head, emit, child))
                    .or_insert_with(|| {
                        let new_id = nodes.len();
                        let mut up = [child; 18];
                        for b in 1..18 {
                            up[b] = nodes[up[b - 1]].up[b - 1];
                        }
                        let acyc = nodes[child].acyc + 1;
                        let emits = nodes[child].emits + usize::from(emit.is_some());
                        nodes.push(VerifyNode {
                            has_stop,
                            head,
                            emit,
                            next: child,
                            on_cycle: false,
                            run,
                            jump,
                            up,
                            acyc,
                            emits,
                        });
                        new_id
                    });
                node_of.insert(ty, Some(id));
                child = id;
            }
            Some(child)
        };

        let m = items.len();
        let mut run_end = vec![m; m];
        let mut run_start = vec![0; m];
        {
            let mut i = 0;
            while i < m {
                let mut j = i + 1;
                while j < m && items[j] == items[i] {
                    j += 1;
                }
                for k in i..j {
                    run_end[k] = j;
                    run_start[k] = i;
                }
                i = j;
            }
        }

        let mut eval_memo: HashMap<(usize, usize), Option<bool>> = HashMap::new();
        let mut jump_memo: HashMap<(usize, usize, bool), usize> = HashMap::new();
        let mut last_miss_memo: HashMap<usize, Option<usize>> = HashMap::new();
        let mut pass_memo: HashMap<(usize, usize), Option<usize>> = HashMap::new();

        let mut row_states: Vec<(Row, Option<bool>, Option<usize>)> =
            Vec::with_capacity(atoms.len());
        for row in atoms {
            let h0 = intern_head(&row[0]);
            let head0 = if let Some(&res) = eval_memo.get(&(h0, items[0])) {
                res
            } else {
                let res = self.member_known(items[0], &row[0]).await;
                eval_memo.insert((h0, items[0]), res);
                res
            };
            let root_u = if head0 == Some(false) {
                None
            } else {
                unfold(&row[1], &mut intern_head)
            };
            row_states.push((row, head0, root_u));
        }

        let first_index = async |h: usize,
                                 from: usize,
                                 to: usize,
                                 want: bool,
                                 heads: &[Type],
                                 eval_memo: &mut HashMap<(usize, usize), Option<bool>>,
                                 jump_memo: &mut HashMap<(usize, usize, bool), usize>|
               -> Option<usize> {
            let mut i = from;
            let mut path: Vec<usize> = Vec::new();
            while i < to {
                if let Some(&j) = jump_memo.get(&(h, i, want)) {
                    if j == i {
                        break;
                    }
                    path.push(i);
                    i = j;
                    continue;
                }
                let item = items[i];
                let eval = if let Some(&res) = eval_memo.get(&(h, item)) {
                    res
                } else {
                    let res = self.member_known(item, &heads[h]).await;
                    eval_memo.insert((h, item), res);
                    res
                };
                let b = eval?;
                if b == want {
                    jump_memo.insert((h, i, want), i);
                    break;
                }
                path.push(i);
                i = run_end[i];
            }
            for p in path {
                jump_memo.insert((h, p, want), i);
            }
            Some(i.min(to))
        };

        let last_miss_from_1 = async |h: usize,
                                      heads: &[Type],
                                      eval_memo: &mut HashMap<(usize, usize), Option<bool>>,
                                      last_miss_memo: &mut HashMap<usize, Option<usize>>|
               -> Option<usize> {
            if let Some(&cached) = last_miss_memo.get(&h) {
                return cached;
            }
            let mut p = m;
            let mut ans = 0;
            while p > 1 {
                let r = run_start[p - 1];
                let item = items[r];
                let eval = if let Some(&res) = eval_memo.get(&(h, item)) {
                    res
                } else {
                    let res = self.member_known(item, &heads[h]).await;
                    eval_memo.insert((h, item), res);
                    res
                };
                let Some(b) = eval else {
                    last_miss_memo.insert(h, None);
                    return None;
                };
                if !b {
                    ans = p - 1;
                    break;
                }
                p = r;
            }
            last_miss_memo.insert(h, Some(ans));
            Some(ans)
        };

        // The node `k` links after `u`, for `k` at most the links from `u` to a cycle: jumps of
        // `2^17` while `k` is that large, then one jump per bit (`up` has 18 levels; a jump of
        // `2^18` or more read by its low bits alone would land short).
        let lift = |nodes: &[VerifyNode], mut u: usize, mut k: usize| -> usize {
            while k >= 1 << 17 {
                u = nodes[u].up[17];
                k -= 1 << 17;
            }
            for b in (0..17).filter(|b| (k >> b) & 1 != 0) {
                u = nodes[u].up[b];
            }
            u
        };
        let hint_of: BTreeMap<&Row, ChainHint> = hints.iter().map(|(r, h)| (r, *h)).collect();
        let mut known: BTreeMap<Row, Option<bool>> = BTreeMap::new();
        for (row, head0, root_u) in row_states {
            if head0 == Some(false) {
                known.insert(row, Some(false));
                continue;
            }
            let Some(mut u) = root_u else {
                known.insert(row, None);
                continue;
            };
            // A hint, checked here: the node `k` links after `u` reached on this module's own
            // nodes by binary lifting, with no node on the way that leaves for a loop (`emit`),
            // so the row's lists of length `m` pass through it; then the item there missing its
            // head, or the node holding no list of the rest's length, puts the witness outside.
            if let Some(&hint) = hint_of.get(&row) {
                let reach = |k: usize| -> Option<usize> {
                    if k > nodes[u].acyc {
                        return None;
                    }
                    let w = lift(&nodes, u, k);
                    let emits =
                        nodes[u].emits - nodes[w].emits + usize::from(nodes[w].emit.is_some());
                    (emits == 0).then_some(w)
                };
                let outside = match hint {
                    ChainHint::Miss(i) if (1..m).contains(&i) => match reach(i - 1) {
                        Some(w) => {
                            let h = nodes[w].head;
                            let res = if let Some(&res) = eval_memo.get(&(h, items[i])) {
                                res
                            } else {
                                let res = self.member_known(items[i], &heads[h]).await;
                                eval_memo.insert((h, items[i]), res);
                                res
                            };
                            res == Some(false)
                        }
                        None => false,
                    },
                    ChainHint::Len => reach(m - 1).is_some_and(|w| !nodes[w].has_stop),
                    ChainHint::Miss(_) => false,
                };
                if outside {
                    known.insert(row, Some(false));
                    continue;
                }
            }
            let mut d = 1usize;
            let tail_fits: Option<bool> = 'walk: loop {
                if d == m {
                    break 'walk Some(nodes[u].has_stop);
                }
                if nodes[u].on_cycle && nodes[u].next == u && nodes[u].emit.is_none() {
                    if !nodes[u].has_stop {
                        break 'walk Some(false);
                    }
                    let Some(miss) = first_index(
                        nodes[u].head,
                        d,
                        m,
                        false,
                        &heads,
                        &mut eval_memo,
                        &mut jump_memo,
                    )
                    .await
                    else {
                        break 'walk None;
                    };
                    break 'walk Some(miss == m);
                }
                if !nodes[u].on_cycle && nodes[u].run == 1 && run_end[d] > d + 1 {
                    let item = items[d];
                    let mut stack: Vec<usize> = Vec::new();
                    let mut cur = u;
                    let base_steps: Option<usize> = loop {
                        if nodes[cur].on_cycle {
                            break Some(0);
                        }
                        if let Some(&cached) = pass_memo.get(&(cur, item)) {
                            break cached;
                        }
                        let h = nodes[cur].head;
                        let eval_h = if let Some(&res) = eval_memo.get(&(h, item)) {
                            res
                        } else {
                            let res = self.member_known(item, &heads[h]).await;
                            eval_memo.insert((h, item), res);
                            res
                        };
                        let Some(bh) = eval_h else {
                            break None;
                        };
                        if !bh {
                            pass_memo.insert((cur, item), Some(0));
                            break Some(0);
                        }
                        if let Some((h_emit, _)) = nodes[cur].emit {
                            let eval_e = if let Some(&res) = eval_memo.get(&(h_emit, item)) {
                                res
                            } else {
                                let res = self.member_known(item, &heads[h_emit]).await;
                                eval_memo.insert((h_emit, item), res);
                                res
                            };
                            let Some(be) = eval_e else {
                                break None;
                            };
                            if be {
                                pass_memo.insert((cur, item), Some(0));
                                break Some(0);
                            }
                        }
                        stack.push(cur);
                        cur = nodes[cur].next;
                    };
                    let Some(mut acc) = base_steps else {
                        break 'walk None;
                    };
                    while let Some(v) = stack.pop() {
                        acc += 1;
                        pass_memo.insert((v, item), Some(acc));
                    }
                    let rem_run = (run_end[d] - d).min(m - d);
                    let step_cnt = acc.min(rem_run);
                    if step_cnt > 0 {
                        u = lift(&nodes, u, step_cnt);
                        d += step_cnt;
                        continue 'walk;
                    }
                }
                let k = nodes[u].run.min(m - d);
                let end = d + k;
                let Some(miss) = first_index(
                    nodes[u].head,
                    d,
                    end,
                    false,
                    &heads,
                    &mut eval_memo,
                    &mut jump_memo,
                )
                .await
                else {
                    break 'walk None;
                };
                if let Some((h_emit, h_loop)) = nodes[u].emit {
                    let Some(q_last) =
                        last_miss_from_1(h_loop, &heads, &mut eval_memo, &mut last_miss_memo).await
                    else {
                        break 'walk None;
                    };
                    let reach_end = (miss + 1).min(end);
                    let start = d.max(q_last);
                    if start < reach_end {
                        let Some(hit) = first_index(
                            h_emit,
                            start,
                            reach_end,
                            true,
                            &heads,
                            &mut eval_memo,
                            &mut jump_memo,
                        )
                        .await
                        else {
                            break 'walk None;
                        };
                        if hit < reach_end {
                            break 'walk Some(true);
                        }
                    }
                }
                if miss < end {
                    break 'walk Some(false);
                }
                if k < nodes[u].run {
                    break 'walk Some(nodes[u].has_stop);
                }
                u = nodes[u].jump;
                d = end;
            };
            let fits = match (head0, tail_fits) {
                (Some(false), _) | (_, Some(false)) => Some(false),
                (Some(true), Some(true)) => Some(true),
                _ => None,
            };
            known.insert(row, fits);
        }
        f.eval3(&|row| known.get(row).copied().flatten()) == Some(true)
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
                    let fits = m.fits(&left);
                    if !fits {
                        return Some(false);
                    }
                    return self.member_known(item, &m.item).await;
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
            let Some(a) = p.atoms.names().get(self.s().list_parts(v).1) else {
                return Some(p.atoms.cofinite());
            };
            let f = a.payload.p().tuples.get(2);
            if f.is_leaf() == Some(true) {
                return Some(true);
            }
            // The rest types of the rows whose item type holds the item; the rest is in `x`
            // exactly when it is in one of them.
            let mut next: Option<Type> = None;
            for row in f.union_rows()? {
                // A row whose item type may or may not hold the item leaves the list's
                // membership not known.
                if self.member_known(item, &row[0]).await? {
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

    /// The value of the member `t` of another group built by the search of its group's verdicts
    /// ([`group_verdicts`]), read here with no copy ([`Rep::Of`]), or `Some(None)` when its
    /// verdict is not `Inhabited`, so each reader of a group does not search or build its values
    /// again. Each is a function of the group, whichever type asks first. Only a strict search
    /// reads it, as only one reads verdicts ([`Searching::group_verdict`]).
    fn shared(&'m self, t: &Type) -> Option<Option<usize>> {
        if !t.is_member() || !self.s().strict || DECIDING.with(|d| d.borrow().contains(t)) {
            return None;
        }
        if let Some(&r) = self.s().reps.get(t) {
            return Some(r);
        }
        if t.verdict() != Verdict::Inhabited {
            self.s().reps.insert(t.clone(), None);
            return Some(None);
        }
        let (store, at) = SHARED.with(|m| m.borrow().get(t).copied())?;
        let mut s = self.s();
        let r = s.foreign(store, at, Some(t.clone()));
        s.reps.insert(t.clone(), Some(r));
        Some(Some(r))
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
        if let Some(r) = self.shared(t) {
            return Stack::ready(r);
        }
        {
            let mut s = self.s();
            if let Some(&r) = s.reps.get(t) {
                // A type being built, met again through a closure taken to have a value since
                // its build began, is built again inside it: the closure holds no value of its
                // value type, so the value sought there is not part of the one being built, and
                // need not be finite apart from it. A failure kept before such a closure was
                // taken, which read the missing value of another type, is sought again too: it
                // was kept because that type had no value yet, perhaps only because it was being
                // built when read, which depends on the order the types are met in, and the
                // closure may give it one (GROUP-closure-order). Each type is built again so once
                // in its outermost build, and each kept failure once, which bounds the builds at
                // three times those without.
                let nested = r.is_none()
                    && s.assuming.last().is_some_and(|&a| match s.building.get(t) {
                        Some(b) => !b.again && a > b.since,
                        None => (s.provisional.get(t)).is_some_and(|&(at, again)| !again && a > at),
                    });
                // Complexity tradeoff (COMPLEXITY.md K35): a failure kept past a fork tried no
                // candidate at the parts that met a fork, so it says nothing of the search of
                // `t` not past a fork. Read there, it made the answer depend on whether `t` was
                // first met past a fork or not, which follows the order of the atoms (2431 of the meets sweep). Such a failure is kept apart and `t` is built again
                // when sought not past a fork: each type is built at most once in each of the two
                // states, so the builds are at most twice those without. Given up: nothing.
                let unforked = r.is_none() && !s.past_fork && s.past_failures.contains_key(t);
                if !nested && !unforked {
                    if r.is_none() {
                        s.read.push(t.clone());
                    }
                    return Stack::ready(r);
                }
            }
        }
        let t = t.clone();
        self.stack.call(move || async move {
            let (mark, resting, outer) = {
                let mut s = self.s();
                s.reps.insert(t.clone(), None);
                s.past_failures.remove(&t);
                let since = s.assumed;
                let b = s.building.entry(t.clone()).or_insert(Building {
                    depth: 0,
                    since,
                    again: false,
                });
                b.again |= b.depth > 0;
                b.depth += 1;
                if let Some(p) = s.provisional.get_mut(&t) {
                    p.1 = true;
                }
                (s.built.len(), s.resting, std::mem::take(&mut s.read))
            };
            let saved = {
                let mut s = self.s();
                let past = s.past_fork;
                let blame_search = (s.blame.is_some() && !s.open_forks).then(|| {
                    let types_mark = s.push_open_forks();
                    (
                        std::mem::replace(&mut s.refuse_forks, false),
                        std::mem::replace(&mut s.open_forks, true),
                        s.current.take(),
                        types_mark,
                    )
                });
                (past, blame_search)
            };
            let r = self.find_rep(&t).await;
            {
                let mut s = self.s();
                s.past_fork = saved.0;
                if let Some((refuse_forks, open_forks, current, types_mark)) = saved.1 {
                    if let Some(mark) = types_mark {
                        s.pop_open_forks(mark);
                    }
                    s.refuse_forks = refuse_forks;
                    s.open_forks = open_forks;
                    s.current = current;
                }
            }
            let again = {
                let mut s = self.s();
                let b = s.building.get_mut(&t).expect("a build under way is listed");
                b.depth -= 1;
                if b.depth == 0 {
                    s.building.remove(&t);
                }
                // A value found by the build inside this one, and kept, is a value of `t`, and is
                // already listed as built.
                let inner = s.reps.get(&t).copied().flatten().filter(|_| r.is_none());
                let r = r.or(inner);
                s.reps.insert(t.clone(), r);
                if r.is_none() && s.past_fork {
                    s.past_failures.insert(t.clone(), ());
                }
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
                        let at = s.assumed;
                        let mut provisional = false;
                        for x in read.into_iter().filter(|x| *x != t) {
                            provisional = true;
                            s.waiting.entry(x).or_default().push(t.clone());
                        }
                        if provisional {
                            s.provisional.entry(t.clone()).or_insert((at, false)).0 = at;
                        }
                        s.read.push(t.clone());
                    }
                    Some(again)
                } else {
                    if inner.is_none() {
                        s.built.push(t.clone());
                    }
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
                if s.reps.get(&y) != Some(&None) || s.building.contains_key(&y) {
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

    /// Whether each of `keys` is empty: known empty without a search, or proved so here
    /// ([`Searching::no_key`]).
    async fn no_keys(&'m self, keys: &[Type]) -> bool {
        for k in keys {
            if !known_empty(k) && !self.no_key(k).await {
                return false;
            }
        }
        true
    }

    /// Whether the key type `k` of a closure is proved empty for good in this search, so the
    /// closure is never called and needs no return value. `k` is decided as the value type of
    /// a morphism is ([`Searching::no_value`]): a decision that reads nothing still being
    /// decided is settled at once, so a nest of morphisms, each the key type of the next, is
    /// decided in the one walk of the search, each key type once. A key type whose decision
    /// reads a type still being decided is proved empty, if it is, at the end of the phase.
    /// While a seed is sought nothing is decided, since that search keeps no answer.
    async fn no_key(&'m self, k: &Type) -> bool {
        // Complexity tradeoff (COMPLEXITY.md K60): the naive version decides each key type by a
        // search of its own, which reads the nest below it again: a nest of d morphisms, each
        // the key type of the next, costs O(d²) (inferred from the structure, not measured).
        // Used: the key type is decided in this search as a value type is, each key type once,
        // O(d) for the nest. Given up: a key type whose decision reads a type still being
        // decided is proved empty only at the end of the phase, and none is proved empty while
        // a seed is sought, so the closure that needs it may be left unbuilt and its member
        // refused (`Refusal::NoWitness`).
        if self.s().seeding {
            return false;
        }
        let walking = std::mem::replace(&mut self.s().walking, true);
        let b = self.no_value(k).await;
        self.s().walking = walking;
        b
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
            if s.building.contains_key(v) {
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

    /// A tuple in every cofinite integer row, when that valuation makes the
    /// row formula true. No emptiness conclusion follows on another carrier.
    // Complexity tradeoff: enumerating each row's shared excluded set costs
    // O(r*l) entries for r rows sharing l boundaries. Instead visit each field
    // once and use its greatest exclusion, O(P + U log S) ordered-set work for
    // P field incidences, U distinct field nodes and largest set size S.
    // Zero is kept when it fits every field. Otherwise 1, or twice the greatest
    // positive exclusion, exceeds every exclusion. Doubling preserves symbolic
    // powers and costs their encoding once. No answer is given up in this
    // cofinite, all-rows-true class; other fields keep the original search.
    // Tests: distinct_integer_columns_reuse_a_checked_point,
    // shared_cofinite_boundaries_are_not_enumerated_per_row, and the symbolic
    // integer scaling test.
    fn cofinite_integer_rep(&self, len: usize, whole: &Part<Row>) -> Option<usize> {
        if len == 0 || whole.eval3(&|_| Some(true)) != Some(true) {
            return None;
        }
        let rows = whole.distinct_atoms();
        if rows.is_empty() {
            return None;
        }
        let mut seen = HashSet::<u64, Digests>::default();
        let mut fields = Vec::new();
        for row in &rows {
            for t in row {
                if !seen.insert(t.node_id()) {
                    continue;
                }
                let Node::Parts(p, _) = &*t.0 else {
                    return None;
                };
                if !p.scalars_only()
                    || p.bools != 0
                    || !p.ints.cofinite
                    || [&p.rats, &p.floats, &p.f32s, &p.strings]
                        .iter()
                        .any(|l| l.cofinite || !l.values.is_empty())
                {
                    return None;
                }
                fields.push(&p.ints);
            }
        }
        let zero = Value::Int(0);
        let value = if fields.iter().all(|l| l.contains(&zero)) {
            zero
        } else {
            let mut greatest = &zero;
            for l in fields {
                if let Some(v) = l.values.last()
                    && v != greatest
                    && v > greatest
                {
                    greatest = v;
                }
            }
            if greatest == &zero {
                Value::Int(1)
            } else {
                Value::integer(greatest.as_integer()?.twice_integer())
            }
        };
        let mut s = self.s();
        let v = s.show(Rep::Value(value));
        Some(s.show(Rep::Tuple(vec![v; len])))
    }

    /// Tries a checked common point first, then distinct choices per column.
    // Complexity tradeoff: enumerating scalar boxes is exponential in the rows.
    // Instead intersect mandatory integer constraints and avoid the other finite
    // boundaries, O(s log s) per distinct column signature in its field
    // incidences and boundary entries, and try one fresh integer per uniform column.
    // Mixed carriers and candidates needing another recursive fork are left to the
    // existing search. No Empty answer follows from failure. Exercised by
    // parity_verdicts_scale_with_the_number_of_constraints, the name/order test,
    // and shared_integer_columns_scale_with_their_written_dag. Distinct columns
    // can still repeat shared boundary work; this is not a whole-DAG bound.
    async fn fresh_integer_rep(&'m self, len: usize, whole: &Part<Row>) -> Option<usize> {
        if let Some(v) = self.cofinite_integer_rep(len, whole) {
            return Some(v);
        }
        // This selects a candidate; the two evaluations do not prove monotonicity.
        if whole.eval3(&|_| Some(false)) != Some(false)
            || whole.eval3(&|_| Some(true)) != Some(true)
        {
            return None;
        }
        let rows = whole.distinct_atoms();
        let mandatory: BTreeSet<Row> = whole.forced_factors().into_iter().collect();
        let mut point = vec![None; len];
        let mut chosen = false;
        // A column's scalar choice depends only on its distinct fields and on
        // whether each is required. Compare those inputs by Type value, not address.
        // Reusing a column reuses its point rather than walking its literal sets again.
        let mut points: BTreeMap<Vec<(&Type, bool)>, Option<Value>> = BTreeMap::new();
        for j in 0..len {
            let mut fields: BTreeMap<&Type, bool> = BTreeMap::new();
            let (mut integer, mut cofinite) = (true, false);
            for row in &rows {
                let required = mandatory.contains(row);
                let field = &row[j];
                if let Some(taken) = fields.get_mut(field) {
                    *taken |= required;
                    continue;
                }
                let p = field.p();
                if !p.scalars_only()
                    || p.bools != 0
                    || [&p.rats, &p.floats, &p.f32s, &p.strings]
                        .iter()
                        .any(|l| l.cofinite || !l.values.is_empty())
                {
                    integer = false;
                    break;
                }
                cofinite |= p.ints.cofinite;
                fields.insert(field, required);
            }
            if !integer || !cofinite {
                continue;
            }
            let signature: Vec<_> = fields.into_iter().collect();
            if let Some(value) = points.get(&signature) {
                point[j] = value.clone();
                chosen |= point[j].is_some();
                continue;
            }
            let mut mentioned = BTreeSet::new();
            let mut allowed = Lits {
                cofinite: true,
                ..Lits::default()
            };
            for &(field, required) in &signature {
                let p = field.p();
                if required {
                    allowed = allowed.zip(&p.ints, super::Op::And);
                } else {
                    mentioned.extend(p.ints.values.iter().cloned());
                }
            }
            let mut i = num_bigint::BigInt::from(0);
            point[j] = if allowed.cofinite {
                Some(loop {
                    let value = Value::int(i.clone());
                    if !mentioned.contains(&value) && allowed.contains(&value) {
                        break value;
                    }
                    i += 1;
                })
            } else {
                allowed
                    .values
                    .iter()
                    .find(|v| !mentioned.contains(*v))
                    .cloned()
            };
            chosen |= point[j].is_some();
            points.insert(signature, point[j].clone());
        }
        if !chosen {
            return None;
        }
        // A shared row can occur at several diagram nodes. Test its fields once;
        // restriction then uses a lookup, not another walk of those same fields.
        let misses: BTreeSet<&Row> = rows
            .iter()
            .filter(|row| {
                point
                    .iter()
                    .enumerate()
                    .any(|(j, v)| v.as_ref().is_some_and(|v| !row[j].p().ints.contains(v)))
            })
            .collect();
        let residual = whole.restrict(&|row| misses.contains(&row).then_some(false));
        if residual.is_leaf() == Some(false) {
            return None;
        }
        // Intersect every remaining row for this one candidate, rather than computing
        // the mandatory rows. This can miss a witness, so row_rep still checks it.
        let taken = residual.distinct_atoms();
        let row: Vec<Type> = point
            .iter()
            .enumerate()
            .map(|(j, v)| match v {
                Some(v) => Type::lit(v).expect("an integer has a literal type"),
                None => Type::meet_all(taken.iter().map(|a| a[j].clone())),
            })
            .collect();
        let forked = (0..len).any(|j| {
            let mut cells = rows.iter().map(|a| &a[j]).filter(|t| t.is_recursive());
            cells.next().is_some_and(|a| cells.any(|b| b != a))
        });
        let past = self.s().past_fork;
        if past && forked {
            return None;
        }
        if forked {
            self.s().past_fork = true;
        }
        let found = self.row_rep(&row, whole).await;
        self.s().past_fork = past;
        found
    }

    async fn find_rep(&'m self, t: &Type) -> Option<usize> {
        // A bare atom is a value: the empty list of a list type.
        // The least bare name, as a scan of `names` in order found it: O(log n) from the index
        // of bare names (`Atoms::bare`), where the scan read every name before it.
        if let Some(name) = t.p().atoms.bare().get_min() {
            return Some(self.s().show(Rep::Value(Value::atom(name))));
        }
        // A list of pure cycles with no stop in it: a list of it, kept as its length. A union of
        // cycles the rule on residues does not decide is left to the rules below.
        if let Some(m) = self.cycle_meet(t).await {
            let r = self.cycle_rep(&m).await;
            if r.is_some() || m.any.is_empty() || m.lengths().is_some() {
                return r;
            }
        }
        // A root list in the front sweep's class: its checked value, or none when it is empty.
        if let Some(r) = self.swept(t) {
            return r;
        }
        // A list of a carrier cycle less prefix chains: a witness list from the sweep,
        // verified independently by `check_chain_witness` before being returned.
        if !self.in_fallback(t)
            && let Some(plan) = self.prefix_chains(t).await
        {
            match plan {
                ChainPlan::Empty => return None,
                plan @ ChainPlan::Inhabited { .. } => {
                    if let Some(r) = self.chain_rep(t, plan).await {
                        return Some(r);
                    }
                    self.s().chains.insert(t.clone(), None);
                }
            }
        }
        let p = t.p();
        if p.bools != 0 {
            return Some(self.s().show(Rep::Value(Value::Bool(p.bools & 1 == 0))));
        }
        // A cofinite set of a carrier holds one of the first values not listed in it.
        type Fresh = fn(i64) -> Value;
        let fresh: [(&Lits, Fresh); 5] = [
            (&p.ints, Value::Int),
            (&p.strings, |i| Value::str(&i.to_string())),
            (&p.rats, |i| Value::rat(crate::Rat::int(i.into()))),
            (&p.floats, |i| Value::float(i as f64)),
            (&p.f32s, |i| Value::float32(i as f32)),
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
        if p.atoms.cofinite() {
            let name = (0..)
                .map(|i| format!("a{i}"))
                .find(|n| !p.atoms.names().contains_key(n.as_str()));
            let name = name.expect("a name is free");
            return Some(self.s().show(Rep::Value(Value::atom(&name))));
        }
        let list_fallback =
            matches!(self.s().chains.get(t), Some(None)) && !self.s().wraps.contains_key(t);
        for (name, a) in p.atoms.names() {
            if a.bare {
                return Some(self.s().show(Rep::Value(Value::atom(name))));
            }
            if list_fallback {
                self.s().in_list_fallback += 1;
            }
            let r = self.rep(&a.payload).await;
            if list_fallback {
                self.s().in_list_fallback -= 1;
            }
            if let Some(r) = r {
                let tuple = {
                    let mut s = self.s();
                    let l = s.local(r);
                    matches!(s.shown[l], Rep::Tuple(_))
                };
                if tuple {
                    return Some(self.s().show(Rep::Atom(name.clone(), r)));
                }
            }
        }
        if p.structs {
            return Some(self.s().show(Rep::Struct));
        }
        let mixed = !p.atoms.is_default() || !p.tuples.is_default();
        if mixed && p.morphisms.is_leaf() != Some(false) {
            // Complexity tradeoff: n mixed types can share one union of n
            // morphisms. Enumerating that union for each type costs O(n^2).
            // Give the shared carrier one Type and use the existing value
            // memo and retry worklist, O(1) expected lookup per occurrence,
            // plus the union's own search. Node numbers are never addresses.
            // This tries the same carrier first; other carriers still follow
            // when no closure is found. Test: shared_morphism_constraints_scale_beside_a_refused_member.
            let carrier = self
                .s()
                .morphism_types
                .entry(p.morphisms.id())
                .or_insert_with(|| Type::with(|q| q.morphisms = p.morphisms.clone()))
                .clone();
            if let Some(v) = self.rep(&carrier).await {
                return Some(v);
            }
        } else if p.morphisms.is_leaf() != Some(false) {
            let top = Morphism::new(Type::empty(), Type::top(), Type::top());
            // A closure is shown only for a meet of morphism types whose keys are all
            // permitted as written and whose value type has a value, which may be one being
            // built here, holding this closure: a closure can return itself. A closure whose
            // keys are empty, known so or proved so in this search, is shown for any value type,
            // since it is never called; its keys are decided only when they are not permitted as
            // written or its value type has no value, so a closure that returns a value costs no
            // decision of its keys. The
            // keys of a meet are the union of its morphism types' keys, so they are empty when
            // each of those is; each is read as written, since a recursive type and its
            // unfolding are compared as different types. A meet of one morphism type is that type
            // as written: its meet with the top one would give the unfolding of a recursive value
            // type, which is neither the type being built nor one its group decided.
            let (taken, refused) = p.morphisms.forced();
            let whole = refused.is_empty() && taken.len() == p.morphisms.distinct_atoms().len();
            // The keys of the types taken that every row of a meet with a union shares.
            let mut shared: Vec<Type> = Vec::new();
            let meets: Vec<(Morphism, Vec<Type>)> = match (whole, p.morphisms.union_rows()) {
                (true, _) => vec![(
                    match taken.split_first() {
                        Some((a, rest)) => rest.iter().fold(a.clone(), |r, b| {
                            let join = |x: &Type, y: &Type| {
                                if x.is_recursive() && y.is_recursive() && x == y {
                                    x.clone()
                                } else {
                                    self.cut(x, y, Cut::Join)
                                }
                            };
                            let both = |x: &Type, y: &Type| {
                                if x.is_recursive() && y.is_recursive() && x == y {
                                    x.clone()
                                } else {
                                    self.cut(x, y, Cut::Meet)
                                }
                            };
                            Morphism::new(
                                join(&r.guarantee, &b.guarantee),
                                both(&r.permission, &b.permission),
                                both(&r.value, &b.value),
                            )
                        }),
                        None => top,
                    },
                    taken.iter().map(|a| a.guarantee.clone()).collect(),
                )],
                (false, Some(rows)) => (rows.into_iter())
                    .map(|m| {
                        let keys = vec![m.guarantee.clone()];
                        (m, keys)
                    })
                    .collect(),
                // A meet of the morphism types every value takes with a union of morphism types:
                // a closure for each arm of the union, met with the types taken. The meet of the
                // types taken and their keys are found once and shared by the arms, so the rows
                // cost the part's size plus one meet per arm. Each atom is read as written, so two
                // atoms that denote one type (a meet written in two orders) give two rows of one
                // meaning, and either may be built.
                // Complexity tradeoff: the arms are not compared with each other or with the types
                // taken, so a meet that is empty only in combination with a later arm is found by
                // the search below, not here; comparing arms pairwise would cost the square of
                // their number.
                (false, None) if refused.is_empty() && !taken.is_empty() => {
                    let set: BTreeSet<&Morphism> = taken.iter().collect();
                    let rest = p.morphisms.restrict(&|a| set.contains(a).then_some(true));
                    let (a, more) = taken.split_first().expect("a type is taken");
                    let met = more.iter().fold(a.clone(), |r, b| self.meet(&r, b));
                    shared = taken.iter().map(|a| a.guarantee.clone()).collect();
                    (rest.union_rows().unwrap_or_default().into_iter())
                        .map(|a| (self.meet(&met, &a), vec![a.guarantee.clone()]))
                        .collect()
                }
                (false, None) => Vec::new(),
            };
            // Whether the shared keys are known empty, and whether they are proved empty, asked
            // once for all rows. A key proved empty later in the search is then missed by the
            // rows after the first ask, which leaves the closure unbuilt, never a wrong value.
            // Complexity tradeoff: one ask for all rows instead of one per row keeps the rows
            // linear in the number of arms, at the cost of the late proofs just named.
            let shared_known = shared.iter().all(known_empty);
            let mut shared_none: Option<bool> = shared_known.then_some(true);
            for (m, keys) in &meets {
                if keys.iter().all(known_empty) && shared_known {
                    return Some(self.s().show(Rep::Closure(m.clone())));
                }
                // The promised keys lie within the permitted ones when their difference, built as
                // a type with no search, is the empty type as written (X45: `{0}` within `int`).
                // That reads no answer still being decided and runs no user code.
                // Complexity tradeoff: one difference of the two key types, O(their size), per
                // row; a difference that is empty only by a search (recursive keys) is not
                // found here, and the closure is then left to `no_keys` as before.
                let permitted = m.guarantee == m.permission
                    || m.guarantee == Type::empty()
                    || m.permission == Type::top()
                    || &m.guarantee - &m.permission == Type::empty();
                if !permitted {
                    if self.no_keys(keys).await {
                        let none = match shared_none {
                            Some(b) => b,
                            None => *shared_none.insert(self.no_keys(&shared).await),
                        };
                        if none {
                            return Some(self.s().show(Rep::Closure(m.clone())));
                        }
                    }
                    continue;
                }
                {
                    let mut s = self.s();
                    if let Some(values) = s.optimistic.as_mut() {
                        values.push(m.value.clone());
                        return Some(s.show(Rep::Closure(m.clone())));
                    }
                }
                // What the closure returns may hold the closure, at any depth, and the value
                // being built that holds the closure ([`Searching::rep`]).
                let mark = {
                    let mut s = self.s();
                    let mark = s.built.len();
                    let closure = s.show(Rep::Closure(m.clone()));
                    s.reps.insert(t.clone(), Some(closure));
                    s.assumed += 1;
                    let a = s.assumed;
                    s.assuming.push(a);
                    mark
                };
                let returns = self.returnable(&m.value).await;
                {
                    let mut s = self.s();
                    s.assuming.pop();
                    s.reps.insert(t.clone(), None);
                    if returns {
                        return Some(s.show(Rep::Closure(m.clone())));
                    }
                    for x in s.built.split_off(mark) {
                        s.reps.remove(&x);
                    }
                }
                if self.no_keys(keys).await {
                    let none = match shared_none {
                        Some(b) => b,
                        None => *shared_none.insert(self.no_keys(&shared).await),
                    };
                    if none {
                        return Some(self.s().show(Rep::Closure(m.clone())));
                    }
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
            for (len, f) in &p.tuples.lens {
                if let Some(v) = self.fresh_integer_rep(*len, f).await {
                    return Some(v);
                }
                // A row the part excludes is skipped: its value is in that tuple type, and every
                // tuple of the part is in none of the excluded ones (`Part::forced`), so the
                // value would fail `holds` against the part.
                // Complexity tradeoff (COMPLEXITY.md K126): the naive seeding builds a value for
                // each of the r rows and tests it against all r rows, O(r²) membership tests,
                // each of which walks the value's list against the row's list type: on a list
                // type less r list types (`emptiness_counts_a_fork_as_inhabited_in_its_size`)
                // that was 41,539 (value, type) pairs at r about 130. Used: the excluded rows,
                // found once in O(r log r) (`Part::forced`), are not tried, which leaves the
                // rows that may hold a tuple of the part; on a difference `a - (b1 | ... | bn)`
                // that is `a` alone, O(r) tests. Given up: nothing, since a value of an
                // excluded row is never a value of the part; a formula whose rows are not
                // forced (a union of differences) is tried row by row as before.
                let (_, excluded) = f.forced();
                let excluded: BTreeSet<&Row> = excluded.iter().collect();
                for row in f.distinct_atoms() {
                    if excluded.contains(&row) {
                        continue;
                    }
                    if let Some(v) = self.row_rep(&row, f).await {
                        return Some(v);
                    }
                }
            }
            return None;
        }
        let past = self.s().past_fork;
        for (len, whole) in &p.tuples.lens {
            if whole.union_rows().is_some() {
                continue;
            }
            // Complexity tradeoff: enumerating all scalar boxes branches exponentially.
            // One point outside the finite integer boundaries costs O(L log L) for L
            // literals, respecting exposed mandatory finite bounds; it reduces the row formula
            // once and meets residual fields in
            // pairs. Nothing is given up: row_rep checks the candidate, and failure
            // proceeds to the old search. Nested fork candidates retain the existing
            // past_fork rule. Test: setop::parity_verdicts_scale_with_the_number_of_constraints.
            if let Some(v) = self.fresh_integer_rep(*len, whole).await {
                return Some(v);
            }
            let forks = self.s().kept_forks;
            let (mut whole_box, mut narrowed) = (
                self.region(vec![Type::top(); *len], whole).await,
                whole.clone(),
            );
            if self.narrow_tuples(&mut whole_box, &mut narrowed).await {
                continue;
            }
            // A part that is, on its box, a union of parts that share no tuple type is searched
            // one part at a time on that box: a value of one in the box is a value of the union,
            // and each part's own box holds its own tuple types only, so `n` such parts cost
            // order `n`, not the `n` candidates by `n` cells of one box over them all
            // (`l01_23_groups_and_refusals::refusals::a_union_of_forked_differences_is_refused_in_its_size`,
            // and `a_pair_type_met_with_forked_differences_is_refused_in_its_size`, whose pair
            // type holds the box and so drops out; COMPLEXITY.md K80).
            // Complexity tradeoff (COMPLEXITY.md K80): the naive search narrows each of the n
            // candidates of the whole part against the n cells of its components and then
            // refines each open tuple type, O(n²) narrowings. Used: the split into disjoint
            // disjuncts, the skip of candidates inside an excluded tuple type
            // (`inside_excluded`) and the proof below that a part whose candidates all lie
            // inside excluded tuple types is empty, O(n) for these forms. Given up: nothing for
            // a part these cover; a forked part not so proved empty is refined as before, at
            // its old cost, so a value only refining finds is kept.
            let split = narrowed.disjoint_disjuncts();
            let parts = split.clone().unwrap_or_else(|| vec![whole.clone()]);
            for f in &parts {
                self.s().past_fork = past;
                // Where `refine` starts: a part of the split stands for the union on the box only.
                let start = match split {
                    Some(_) => whole_box.r.clone(),
                    None => vec![Type::top(); *len],
                };
                let (mut b, g) = match split {
                    Some(_) => {
                        let (mut b, mut g) = (self.region(start.clone(), f).await, f.clone());
                        if self.narrow_tuples(&mut b, &mut g).await {
                            continue;
                        }
                        (b, g)
                    }
                    None => (std::mem::take(&mut whole_box), narrowed.clone()),
                };
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
                // A part of one choice per component: the choice the one pass finds, checked
                // as any candidate is (step EMPTY-overlap-fast). It replaces the candidate for
                // each tuple type below, a narrowing of the box each, order `c²` for `c` cells.
                let open: Vec<usize> = g.distinct_atoms().iter().map(|a| b.index[a]).collect();
                match self.one_pass_row(&b, &g, &open).await {
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
                // Complexity tradeoff: past a fork, a value is sought through one candidate
                // per tuple type left, once on each path: in a part that met a fork while a
                // value is sought for a candidate past another, no candidate is tried, and the
                // part counts as having none. Why: each candidate seeks values of its
                // components, each a new difference that meets the fork again one element
                // further on, so the search went as deep as the forked lists are long, each
                // level testing every tuple type left: order n^2 on the lists against a 1 at
                // each place from the end up to `n` (63,634 `cuts` at `n` 64; now 1,578).
                // Trigger: a narrowing of this part kept a component whole at a fork while
                // `past_fork`. Tests:
                // `l01_23_groups_and_refusals::refusals::bench::a_union_of_lists_by_the_place_of_a_one_is_refused_in_its_size`
                // and `a_value_is_sought_before_a_refusal` (`fork`, found by a candidate past
                // the first fork). COMPLEXITY.md K35. A complete solution needs the subset
                // construction over the forked tuple types, exponential in them. Used: one
                // candidate per tuple type once per path; the end family takes 1,578 `cuts` at
                // `n` 64 against 63,634 without `past_fork` (K35 control, 50 times from 8 to 64).
                // A fork can remain open without leaving a kept emptiness snapshot.
                // Count it before starting another candidate search: one scan of the cells.
                // Abandoning a witness attempt supplies no emptiness proof.
                // Complexity tradeoff (COMPLEXITY.md K102): the scan is O(m k) for m components
                // and k open tuple types, the size of the region read just before it; keeping
                // a count of open forks up to date through every narrowing would save no order.
                let open_fork = (0..b.r.len()).any(|j| b.forks(&open, j));
                let forked = self.s().kept_forks > forks || open_fork;
                if forked {
                    if past {
                        continue;
                    }
                    self.s().past_fork = true;
                }
                // The tuple types the part excludes: a value in one is in no value of the part.
                let (_, excluded) = g.forced();
                let mut refused = vec![false; b.atoms.len()];
                // For each component and cell, the excluded tuple types that have that cell there.
                let mut sharing: Vec<Vec<Vec<usize>>> = b
                    .cells
                    .iter()
                    .map(|cs| vec![Vec::new(); cs.len()])
                    .collect();
                for a in &excluded {
                    let e = b.index[a];
                    refused[e] = true;
                    for (j, cells) in sharing.iter_mut().enumerate() {
                        cells[b.cell(e, j)].push(e);
                    }
                }
                // Complexity tradeoff (COMPLEXITY.md K35, K80): the naive version narrows every
                // candidate, O(n^2) types for n candidates; used, one test per candidate skips
                // those inside an excluded tuple type, O(n) on the pairs of `fork_by`; nothing is
                // given up, the answer is the same.
                // One candidate for each tuple type left, narrowed by what the part says of it. A
                // candidate inside a tuple type the part excludes holds no value of it, and the
                // narrowing or the check of its row would say so, so it is skipped: narrowing it tests
                // every open cell of its components, n candidates by n cells, order n^2 types on the
                // pairs of `l01_23_groups_and_refusals::refusals::fork_by` (COMPLEXITY.md K35). So is a candidate
                // that lies inside an excluded tuple type in every component, as each pair of
                // `a_difference_of_forked_unions_is_refused_in_its_size` does (K80). `all_inside`
                // says whether every candidate was skipped so.
                let mut all_inside = true;
                // Complexity tradeoff (COMPLEXITY.md K135, BENCH-row-rep-many-tuples): when the
                // narrowed part is a plain union of its tuple types (`Part::union_rows`), each
                // candidate is the box met with its tuple type, checked by `row_rep` with no
                // narrowing. Proof that nothing is lost: on the box `b`, `g` is `f` (narrowing
                // only drops values outside `f`), so with `g` the union of the `a`, every value
                // of `b.r & a` is a value of `f`; narrowing the candidate drops only values outside
                // `f`, so it leaves the same values, and `row_rep` searches them either way.
                // Naive version: each candidate narrowed, which tests the changed components
                // against every open cell, `n` candidates by `n` cells: 115,094 cell tests at
                // `n` 128, and the verdict 0.66 s at 64 and 47.3 s at 512, on `n` pairs of a list
                // of `i` and a morphism type with no value built, met with the pairs of a list of
                // integers and any value (71 times the time per 8 times `n`, load about 95).
                // Used: one meet and one `row_rep` per candidate, `O(n)` meets; 37 ms to 338 ms
                // from `n` 64 to 512 (9.1 times, load 74 to 80, debug build). Bench:
                // `refusals::bench::a_plain_union_of_forked_tuple_types_without_values_is_refused_in_its_size`.
                let union = g.union_rows().is_some();
                for a in g.distinct_atoms() {
                    let k = b.index[&a];
                    if refused[k] || self.inside_excluded(&b, k, &sharing).await {
                        continue;
                    }
                    all_inside = false;
                    if union {
                        let row: Vec<Type> = b.r.iter().zip(a.iter()).map(|(x, y)| x & y).collect();
                        if let Some(v) = self.row_rep(&row, f).await {
                            return Some(v);
                        }
                        continue;
                    }
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
                // A part with no value outside its candidates, each candidate inside an excluded
                // tuple type, has no value: the part on the box with every candidate false is
                // false, and an excluded tuple type holds no value of the part. Neither the
                // candidates below nor refining would find one, so nothing is given up, and
                // refining such a part on a fork costs order `n^2`, a search of the whole part for
                // each tuple type (`a_difference_of_forked_unions_is_refused_in_its_size`,
                // COMPLEXITY.md K80). A forked part whose components separate in `overlaps` (`Π_sym`)
                // is already split by `class_rep` above (`a_value_found_by_refining_a_forked_part_is_kept`);
                // skipping `refine` on a still-forked unsplit box prevents order-dependent refusal vs
                // witness selection across forked arms.
                if all_inside
                    && g.restrict(&|a| (!refused[b.index[a]]).then_some(false))
                        .is_leaf()
                        == Some(false)
                {
                    continue;
                }
                // One candidate for each component: the box with that component outside every
                // tuple type the part excludes, so the tuple is in none of them. Pairs of a list
                // and an integer without those of lists of only 1s or only 2s hold `([0], 0)`,
                // whose list is in neither excluded list type.
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
                if !forked {
                    // Complexity tradeoff: on a non-forked union of differences (such as Seed 1908
                    // outside `C_group`, where `b.r` is still `[top, ..]` and default component
                    // representatives hit `#a` or an in-progress member), form the union of
                    // positive rows and subtract the union of negated rows once across `g` in
                    // `O(m * K log K)` time (`K` rows), testing at most `m + 1` sub-boxes instead
                    // of `O(K²)` per-candidate subtractions or `O(K^m)` box complementation.
                    let mut seen_pos = DigestSet::default();
                    let mut pos_set = BTreeSet::new();
                    g.taken_toward(true, &mut seen_pos, &mut |r| {
                        pos_set.insert(r);
                    });
                    let mut seen_neg = DigestSet::default();
                    let mut neg_set = BTreeSet::new();
                    g.taken_toward(false, &mut seen_neg, &mut |r| {
                        neg_set.insert(r);
                    });
                    if !pos_set.is_empty() && !neg_set.is_empty() {
                        let m_len = b.r.len();
                        let mut pos_u = Vec::with_capacity(m_len);
                        let mut safe = Vec::with_capacity(m_len);
                        for j in 0..m_len {
                            let pj =
                                &b.r[j] & &Type::union_all(pos_set.iter().map(|r| r[j].clone()));
                            let nj = Type::union_all(neg_set.iter().map(|r| r[j].clone()));
                            safe.push(&pj - &nj);
                            pos_u.push(pj);
                        }
                        if let Some(v) = self.row_rep(&safe, f).await {
                            return Some(v);
                        }
                        for j in 0..m_len {
                            if safe[j] != pos_u[j] {
                                let mut cand = pos_u.clone();
                                cand[j] = safe[j].clone();
                                if let Some(v) = self.row_rep(&cand, f).await {
                                    return Some(v);
                                }
                            }
                        }
                    }
                    for blind_inside in [true, false] {
                        if let Some(row) = self.refine(start.clone(), f, blind_inside).await
                            && let Some(v) = self.row_rep(&row, f).await
                        {
                            return Some(v);
                        }
                    }
                }
            }
        }
        None
    }

    /// Whether tuple type `k` of the box `b` lies inside an excluded tuple type in every
    /// component: such a candidate holds no value of the part. Only the excluded tuple types
    /// that share `k`'s cell on one component are tried, on the component where fewest do: a
    /// tuple type that holds `k` without sharing a cell with it is not found, and `k` is then
    /// narrowed into as before.
    async fn inside_excluded(&'m self, b: &Region, k: usize, sharing: &[Vec<Vec<usize>>]) -> bool {
        let Some(j) = (0..b.r.len())
            .map(|j| (sharing[j][b.cell(k, j)].len(), j))
            .filter(|&(m, _)| m > 0)
            .min()
            .map(|(_, j)| j)
        else {
            return false;
        };
        for &e in &sharing[j][b.cell(k, j)] {
            let mut inside = true;
            for i in 0..b.r.len() {
                if b.cell(k, i) != b.cell(e, i)
                    && !self.settles(&b.atoms[k][i], &b.atoms[e][i], false).await
                {
                    inside = false;
                    break;
                }
            }
            if inside {
                return true;
            }
        }
        false
    }

    /// A value of the tuple part `g` of length `len` on the box of `b`, sought piece by piece
    /// when the open tuple types fall into classes on a component: on the pieces of
    /// [`Searching::split_classes`], the rest, which no class meets, then one piece per class,
    /// each a type of its own whose box holds only its class in that component. Nothing when
    /// there are no such classes; `Some(None)` when no piece has a value found.
    async fn class_rep(&'m self, b: &Region, g: &Part<Row>, len: usize) -> Option<Option<usize>> {
        let open: Vec<usize> = g.distinct_atoms().iter().map(|a| b.index[a]).collect();
        // The regions of flat keys too (BENCH-region-split-late-failure): every cell holds a
        // region whole or shares no value with it, so a value found in a region's piece is a
        // value of the part, as for a class. Without them, `n` rows `(a | i, a | i)` sharing the
        // atom `a` made one class, and the candidates after this narrowed one tuple type each
        // against every cell: order n² (57.2 times the instructions per 8 times `n` on
        // `diagonal_rows_less_rows_failing_on_the_last_region_scale`, load 37).
        let (j, classes, _) = classes(b, &open, true)?;
        let mut found = None;
        let mut each = Each::Seek {
            len,
            found: &mut found,
        };
        self.split_classes(b, g, j, &classes, &mut each).await;
        Some(found)
    }

    /// A box within the tuple part `f` and the box `start`, found by splitting each component,
    /// one tuple type at a time, into the piece inside that tuple type and the piece outside it,
    /// and keeping a piece the search shows inhabited, else one it does not prove empty. Each
    /// step is at most two searches, and a step is taken again at most once, after the box is
    /// proved empty and its latest blind cut undone, so the searches are at most four times
    /// the tuple types times the components, and the box ends closed on every tuple type: the
    /// part then holds all of it or none. Its searches neither end at a fork nor follow one: a
    /// forked piece counts as inhabited with nothing shown.
    async fn refine(
        &'m self,
        start: Vec<Type>,
        f: &Part<Row>,
        blind_inside: bool,
    ) -> Option<Vec<Type>> {
        // Complexity tradeoff: the searches of `refine` count a part whose open tuple types
        // fork as inhabited, with nothing shown (`open_forks`), as the search of a value after a
        // refused decision does, instead of following the fork. Given up: a value that only a
        // piece past a fork would show; the box then keeps that piece, its row is checked as
        // any candidate is, and the type is refused for `Fork` (the cause met) where no value
        // is found. Why: `refine` turns `refuse_forks` off, so that a fork does not end the
        // search, and with `open_forks` off too its searches followed the fork, the subset
        // construction (the tradeoff in `narrow_tuples`), exponential in the recursive types:
        // the pairs of `W -> int` and lists of length 2, less the pairs of `Never ->? (L | (S,
        // L))` and lists `[1, _]`, nonempty lists or `cons(int, E)` with `E` the end family of
        // `n` places, cost 28.5M, 320M and 3.64G instructions at `n` 1, 2 and 3 (`is_empty`
        // 1.58G at 3); now 62.1M and 435M at 8 and 64. Trigger: a fork met in a piece `refine`
        // tries, in a search with `refuse_forks` set (`verdict_alone`, `is_empty`). Test:
        // `l01_23_groups_and_refusals::refusals::refining_a_box_follows_no_fork_in_its_size`.
        // COMPLEXITY.md K35. A complete solution needs the subset construction over the
        // forked tuple types, exponential in them.
        let (refuse_forks, open_forks, types_mark) = {
            let mut s = self.s();
            let refuse = std::mem::replace(&mut s.refuse_forks, false);
            let open = std::mem::replace(&mut s.open_forks, true);
            let mark = if !open { s.push_open_forks() } else { None };
            (refuse, open, mark)
        };
        let len = start.len();
        let mut g = self.region(start, f).await;
        let mut h = f.clone();
        let mut empty = self.narrow_tuples(&mut g, &mut h).await;
        // Complexity tradeoff (COMPLEXITY.md K133): one pass over the `m * k` pairs (`m`
        // components, `k` open tuple types), each cut at once, on the box the cuts before it
        // shrank, to the side `cut_piece` proves (the other side empty, or this one inhabited),
        // else blindly: to `inside` when `blind_inside`, else to `outside`. When `narrow_tuples`
        // then proves the box empty, the pass undoes the cuts back to its latest blind cut,
        // keeps that cut's other side and goes on from the pair after it; it does so once, so
        // it goes over at most `2 m k` pairs, `4 m k` searches. The caller runs a pass of each
        // side, the second only when the first gives no value: at most `8 m k` searches. Hit
        // rates on random 3-CNF (`r3`, 100 seeds per size, against a count of the models by
        // trying every tuple; both verdicts alike), of 68, 64, 68, 70 and 61 inhabited seeds at
        // 8, 10, 12, 14 and 16 bits: the inside pass alone found 65, 61, 59, 52 and 45 (282 of
        // 331), both passes 68, 64, 66, 65 and 48 (311); with the undo the inside pass alone
        // finds 68, 63, 68, 65 and 53 (317), both passes 68, 64, 68, 70 and 56 (326); the 5 left
        // (seeds 19, 26, 30, 59 and 96 at 16 bits) are refused. The benches (seed 7, 16 and 128
        // bits, refused at both) take 40.6 times the instructions per 8 times the bits with the
        // undo against 43.7 without it, limit 84 (18.9G against 18.0G instructions at 128 bits;
        // order3b, 2026-11-19, load5 21 to 27). Rejected: undoing every blind cut once, the
        // latest one not yet undone at each proof of emptiness, found 327 (seed 26 at 16 bits
        // too) for the same work on the benches, but goes over the pairs from each undone cut
        // again, `O(m² k²)` searches in the worst case. Polarity by the excluded tuple types a
        // side leaves missing the box (Jeroslow-Wang weights `2^-l`) changed no cut: the part
        // forces none of them at a blind cut, so both sides scored 0. No number of passes or
        // undos, nor any rule of polynomial work, finds a value wherever there is one: that
        // would find a model of every satisfiable 3-CNF in polynomial time, deciding 3-SAT,
        // which no rule can do unless P = NP. Backtracking over every blind cut is complete but
        // exponential in them. Miss: `r3(16, 19)`
        // (`random_3_cnf_found_by_a_second_pass_or_an_undone_cut_or_refused`). Tried and
        // rejected (order2's option 2b): defer an unproved pair instead of the blind cut and
        // retry the deferred pairs while some cut happened since their last try. On
        // `the_verdict_of_random_3_cnf_is_refused_in_its_size` (seed 7) that ran 2126 searches
        // from `try_piece` at 128 bits against 86 for one pass, each reading about the same
        // region (about 256 tuple types per `tuples_on` call either way), so 231 times the
        // time per 8 times the bits against 39 for one pass, over the limit of 84 (load 41 to
        // 55). The cost was the number of searches, not the size of what each one reads. What
        // the blind cuts give up: a value on the other side of a blind cut that the pass does
        // not undo; the cuts are sound, since `refine` only proposes a box whose row `row_rep`
        // checks. The blind cuts make the box depend on the order of the pairs, under 2b too,
        // whose last pairs were cut the same way.
        // The latest blind cut, while the pass has undone none: its pair, the marks of the log
        // and of the held forks before it, the part before it, and the side it did not keep.
        let mut last: Option<(usize, usize, usize, usize, Part<Row>, Type)> = None;
        let mut undone = false;
        let atoms = g.atoms.len();
        let (mut j, mut k) = (0, 0);
        while j < len && atoms > 0 && !empty {
            if g.is_open(k, j) {
                let piece = match self.cut_piece(&mut g, &h, j, k).await {
                    Some(piece) => piece,
                    None => {
                        let inside = &g.r[j] & &g.atoms[k][j];
                        let outside = &g.r[j] - &g.atoms[k][j];
                        let (keep, other) = if blind_inside {
                            (inside, outside)
                        } else {
                            (outside, inside)
                        };
                        if !undone {
                            let marks = (g.log.len(), g.forked_holds.len());
                            last = Some((j, k, marks.0, marks.1, h.clone(), other));
                        }
                        keep
                    }
                };
                g.shrink(j, piece);
                empty = self.narrow_tuples(&mut g, &mut h).await;
                // The box is proved empty: undo the cuts back to the latest blind one and keep
                // its other side, then go on from the pair after it.
                if empty && let Some((bj, bk, mark, holds, before, other)) = last.take() {
                    undone = true;
                    g.restore(mark);
                    g.forked_holds.truncate(holds);
                    h = before;
                    g.shrink(bj, other);
                    empty = self.narrow_tuples(&mut g, &mut h).await;
                    (j, k) = (bj, bk);
                }
            }
            k += 1;
            if k == atoms {
                (j, k) = (j + 1, 0);
            }
        }
        {
            let mut s = self.s();
            if let Some(mark) = types_mark {
                s.pop_open_forks(mark);
            }
            s.refuse_forks = refuse_forks;
            s.open_forks = open_forks;
        }
        (!empty && h.is_leaf() == Some(true)).then_some(g.r)
    }

    /// For [`Searching::refine`]: the piece of component `j` to keep for the tuple type `k`,
    /// the side of `k` (inside or outside) whose other side the search proves empty or which
    /// it shows inhabited; nothing when neither is proved. At most two searches.
    async fn cut_piece(
        &'m self,
        g: &mut Region,
        h: &Part<Row>,
        j: usize,
        k: usize,
    ) -> Option<Type> {
        let inside = &g.r[j] & &g.atoms[k][j];
        let outside = &g.r[j] - &g.atoms[k][j];
        match self.try_piece(g, h, j, &inside).await {
            (true, _) => Some(outside),
            (false, true) => Some(inside),
            (false, false) => match self.try_piece(g, h, j, &outside).await {
                (true, _) => Some(inside),
                (false, true) => Some(outside),
                (false, false) => None,
            },
        }
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
        self.holds_known(vs.len(), |_, i| vs[i], f).await == Some(true)
    }

    /// Whether the tuple whose component `i` is the value numbered `item(search, i)` is in `f`;
    /// `None` when that rests on the membership of a component that is not known. A tuple is
    /// in a tuple type when each component is in its own, and outside it when one component is
    /// surely outside its own, whichever component that is and whatever is not known of the
    /// others; `f` is then evaluated in three values ([`Part::eval3`]), so a tuple type whose
    /// membership is not known decides nothing only where `f`'s value rests on it. Neither
    /// depends on the order of the components (GROUP-closure-order: a closure whose membership
    /// is not known, met first, made the reversed tuple unknown where a later component was
    /// surely outside). A component is read by number when it is tested, so a tuple among the
    /// values shown is read in place while the tests add to the search.
    // Complexity tradeoff: a tuple of `len` plain values ([`Search::plain`]) is checked on the
    // part's rows filed by the values they may hold ([`RowIndex`], the index
    // `Type::each_value` lists values with): the rows with a key of the tuple are tested, and
    // the part is evaluated again only where they change it from its value on a tuple with no
    // key of any row ([`Graph`](super::Graph)), so a check costs about the rows it may be in
    // times `log r`, after one filing of the part's `r` rows, `O(r log r)`, kept for the
    // search. Naive version, kept for every other tuple: test the tuple against every distinct
    // row and evaluate the whole part, `O(r log r)` per tuple, so `O(r² log r)` when a
    // tuple is tried for each row, as the seeding does (`Searching::find_rep`): the union
    // of `n` differences `(i, int | bool) \ (i, bool)` met with the `n` tuples `(i, bool)`
    // took 1.6 s at `n` = 512, 14.2 s for the subtype test at 1024
    // (FAIL-kernel-empty-tuple-diff-union). The answer is the same: each plain component is
    // a value whose membership in a column `Type::contains` decides, as `member_known` reads
    // it, and a tuple component's as the part of its length decides it, so the part is
    // two-valued on the tuple. Any other tuple with a component that has a key (the last
    // value along its first components and atoms' payloads, a scalar, a bare atom or the empty
    // tuple: [`Search::key`]) is tested only against the rows whose column there lists that
    // key or is not listed ([`Columns`], filed by [`Reading::Payloads`]), the component chosen
    // to leave the fewest; every other row is surely false, so the part is evaluated again
    // only where the rows found to hold change it, or in three values over the tested rows
    // when a membership is not known, `O(r)` then. The pair with the second component
    // `#b((int | bool))` took 1.6 s at `n` = 512 before, 37 ms after
    // (FAIL-kernel-empty-tuple-diff-union); with the first component `#k((i))`, no component
    // a scalar, 1.51 s before, 50 ms after (FAIL-kernel-empty-payload-key-tuple). A row left out
    // gives the answer `member_known` would: along the walk to the key each column is read
    // through its tuple rows' first columns or its atom name's payload type, and a listed
    // column with no such key holds no value with that key, a fact of the values alone, so
    // `member_known` finds it surely outside too. Given up: a tuple none of whose components
    // has a key (each a struct, a closure, a list, or reaching one along its first
    // components) is checked the naive way; and the indexes, their classes, the plain values
    // and the keys are kept for the rest of the search.
    async fn holds_known(
        &'m self,
        len: usize,
        item: impl Fn(&Search, usize) -> usize,
        f: &Part<Row>,
    ) -> Option<bool> {
        let key = (f.expr_id().is_some(), f.id(), len);
        let keys: Vec<Option<Value>> = {
            let mut s = self.s();
            let plain: Option<Vec<Value>> = (0..len)
                .map(|i| {
                    let v = item(&s, i);
                    s.plain(v)
                })
                .collect();
            if let Some(xs) = plain {
                let Search {
                    row_indexes, filer, ..
                } = &mut *s;
                let (_, index) = row_indexes
                    .entry(key)
                    .or_insert_with(|| (f.clone(), RowIndex::new(len, f, filer)));
                let fits = |row: &Row| row.iter().zip(&xs).all(|(t, x)| t.contains(x));
                return Some(index.holds(&xs, fits));
            }
            (0..len)
                .map(|i| {
                    let v = item(&s, i);
                    s.key(v)
                })
                .collect()
        };
        let keyed = keys.iter().any(Option::is_some);
        // The rows to test, with their positions among the rows of `Columns` when a component
        // has a key; every other row is surely false.
        let rows: Vec<(Option<usize>, Row)> = match keyed {
            false => f.distinct_atoms().into_iter().map(|a| (None, a)).collect(),
            true => {
                let mut s = self.s();
                let Search { columns, filer, .. } = &mut *s;
                let (_, c) = columns
                    .entry(key)
                    .or_insert_with(|| (f.clone(), Columns::new(len, f, filer)));
                let at = c.candidates(&keys);
                at.into_iter()
                    .map(|i| (Some(i), c.rows[i].clone()))
                    .collect()
            }
        };
        let mut known: BTreeMap<Row, Option<bool>> = BTreeMap::new();
        let (mut holding, mut unknown) = (Vec::new(), false);
        for (at, a) in rows {
            let mut fits = Some(true);
            for (i, y) in a.iter().enumerate() {
                let v = item(&self.s(), i);
                match self.member_known(v, y).await {
                    Some(true) => {}
                    Some(false) => {
                        fits = Some(false);
                        break;
                    }
                    None => fits = None,
                }
            }
            match (at, fits) {
                (Some(i), Some(true)) => holding.push((i, true)),
                (_, None) => unknown = true,
                _ => {}
            }
            known.insert(a, fits);
        }
        if keyed {
            if !unknown {
                return Some(self.s().columns[&key].1.value(&holding));
            }
            // A row not tested has a column that does not hold its component.
            return f.eval3(&|a| known.get(a).copied().unwrap_or(Some(false)));
        }
        f.eval3(&|a| known.get(a).copied().flatten())
    }

    /// Whether the value numbered `v` is in `u`, or `None` when that is not known. What is not
    /// known is kept as such, so a second test of the pair is not read as a sure "no".
    fn member_known(&'m self, v: usize, u: &Type) -> Deep<'m, Option<bool>> {
        let v = {
            let mut s = self.s();
            if matches!(&s.shown[v], Rep::Of { of: Some(m), .. } if m == u) {
                return Stack::ready(Some(true));
            }
            s.local(v)
        };
        {
            let s = self.s();
            if let Rep::Value(x) = &s.shown[v] {
                return Stack::ready(Some(u.contains(x)));
            }
        }
        // Complexity tradeoff (COMPLEXITY.md K111): the answer is kept by the value's class
        // (`Search::class`), so it is tested once for all values equal to it, at the cost of a
        // class for each value tested, O(1) a part, each kept value's class given once for all
        // searches.
        // Naive version: kept by the value's number. The values of the groups decided first
        // (`group_verdicts`) are each read in under a number of their own, so a value kept by k
        // groups, such as a list of n items that n groups each build, was tested k times against
        // each type: Θ(n³) tests on the x_tail lists of size Θ(n²) (T6-refusal-cost), where by
        // class the tests are those of the distinct values against the types.
        let key = (self.s().class(v), u.clone());
        if let Some(&b) = self.s().members.get(&key) {
            return Stack::ready(b);
        }
        // A value whose height is outside the bounds on the heights of `u`'s values
        // ([`height_bounds`]) is not in `u`, read in O(1) once the bounds are made, where
        // the test below walks the value against `u` level by level: for the lists by the place
        // of a 1 from the end, a list of length `k` tested against each of `n` types `G_i` of
        // least height `2i`, Θ(n²) levels in all (COMPLEXITY.md K126).
        {
            let mut s = self.s();
            if let Some(h) = s.value_height(v)
                && height_bounds(u).is_none_or(|(lo, hi)| h < lo || hi < h)
            {
                s.members.insert(key, Some(false));
                return Stack::ready(Some(false));
            }
        }
        self.stack.call(move || async move {
            let b = {
                let u = &key.1;
                // What the value is, read before any test that adds to the values shown.
                enum Shape<'u> {
                    Known(Option<bool>),
                    Tuple(usize, Part<Row>),
                    Payload(usize, &'u Type),
                    List(usize),
                    Closure(Morphism, &'u Part<Morphism>),
                }
                let up = u.p();
                // `v` is `local`'s answer, which is never `Of` (it returns `v` only when not
                // `Of`, else a value it shows from a rep its loop took that is not `Of`), and a
                // `Value` returned above; `shown` is only pushed to (`show`) while the search
                // runs, so `shown[v]` is still that rep.
                let shape = match &self.s().shown[v] {
                    Rep::Value(_) => unreachable!("a value was read above"),
                    Rep::Of { .. } => unreachable!("a value of another search was read in above"),
                    Rep::Closure(m) => match up.morphisms.is_leaf() {
                        Some(b) => Shape::Known(Some(b)),
                        None => Shape::Closure(m.clone(), &up.morphisms),
                    },
                    Rep::Struct => Shape::Known(Some(up.structs)),
                    Rep::Tuple(vs) => Shape::Tuple(vs.len(), up.tuples.get(vs.len())),
                    Rep::Atom(name, payload) => match up.atoms.names().get(name) {
                        None => Shape::Known(Some(up.atoms.cofinite())),
                        Some(a) => Shape::Payload(*payload, &a.payload),
                    },
                    Rep::List { item, .. } => Shape::List(*item),
                };
                match shape {
                    Shape::Known(b) => b,
                    Shape::Tuple(len, f) => {
                        self.holds_known(len, |s, i| s.tuple_item(v, i), &f).await
                    }
                    Shape::Payload(payload, a) => self.member_known(payload, a).await,
                    Shape::List(item) => self.list_member(v, item, u).await,
                    Shape::Closure(m, f) => Self::closure_member(&m, f),
                }
            };
            self.s().members.insert(key, b);
            b
        })
    }

    /// Whether a closure shown for the morphism type `m` is in the morphism part `f`, or `None`
    /// when that is not known. It is in each morphism type of `f` equal to `m`; for another,
    /// whether `m` lies within it or apart from it is an emptiness check, which inside this
    /// search may rest on an answer still being decided, while a value found is kept for good;
    /// so another morphism type stands as unknown (`eval3`), settling `f` whenever `m` alone
    /// determines its value (as in `m | n` or `!m`).
    fn closure_member(m: &Morphism, f: &Part<Morphism>) -> Option<bool> {
        f.eval3(&|a| (a == m).then_some(true))
    }

    /// Whether every morphism `m` admits is in `n`, by the variance law. With no value, the
    /// empty morphism is the only one, and its domain is the guarantee.
    async fn within(&'m self, m: &Morphism, n: &Morphism) -> bool {
        let prev_sub = std::mem::replace(&mut self.s().in_subtype_check, true);
        let no_value = self.no_value(&m.value).await;
        let ok = self.settles(&n.guarantee, &m.guarantee, false).await
            && (no_value || self.settles(&m.permission, &n.permission, false).await)
            && (no_value
                || self.empty(&m.permission).await
                || self.settles(&m.value, &n.value, false).await);
        self.s().in_subtype_check = prev_sub;
        ok
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
            // The morphism types `r` was met with, which hold it by construction. Tested again,
            // such a type may not be found to hold `r`: the search of a value counts a forked
            // part inhabited, so `r.value - a.value` is not proved empty. It was then forced and
            // met again, each meet a type of its own, with no end (GROUP-search-hang). Each pass
            // that meets takes in a morphism type of `f` not yet met, so the passes are at most
            // the morphism types of `f`, plus one.
            let mut inside: BTreeSet<Morphism> = BTreeSet::new();
            loop {
                if self.no_morphism(&r).await {
                    return true;
                }
                let mut st: BTreeMap<Morphism, Option<bool>> = BTreeMap::new();
                let mut forked_atoms = Vec::new();
                let mut atom_non_empty: BTreeMap<Morphism, (bool, Option<ForkSave>)> =
                    BTreeMap::new();
                for a in f.distinct_atoms() {
                    let s = if inside.contains(&a) {
                        Some(true)
                    } else {
                        let snap = self.fork_snapshot();
                        if self.no_morphism(&self.meet(&r, &a)).await {
                            match self.take_fork(snap, None) {
                                None => Some(false),
                                Some(fork) => {
                                    forked_atoms.push((a.clone(), false, fork));
                                    None
                                }
                            }
                        } else {
                            if snap.is_some() && self.s().canonical_blame {
                                let saved = match self.take_blame_on_false(snap, None) {
                                    None => (false, self.take_all_since(snap)),
                                    Some(gu) => (true, Some(gu)),
                                };
                                atom_non_empty.insert(a.clone(), saved);
                            }
                            let snap = self.fork_snapshot();
                            if self.within(&r, &a).await {
                                match self.take_fork(snap, None) {
                                    None => Some(true),
                                    Some(fork) => {
                                        forked_atoms.push((a.clone(), true, fork));
                                        None
                                    }
                                }
                            } else {
                                self.discard_since(snap);
                                None
                            }
                        }
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
                    r = taken.iter().fold(r, |r, a| self.meet(&r, a));
                    inside.extend(taken);
                    continue;
                }
                if may_cover && f.eval3(&|_| Some(false)) == Some(false) {
                    let atoms = f.distinct_atoms();
                    let mut all_empty = true;
                    let mut forks = Vec::new();
                    let mut blamed_false = Vec::new();
                    for a in &atoms {
                        let piece = f.restrict(&|b| (b == a).then_some(true));
                        if piece.is_leaf() == Some(true) {
                            let (blamed, saved) = atom_non_empty.remove(a).unwrap_or((false, None));
                            if !blamed {
                                if let Some(gu) = saved {
                                    self.restore_fork(gu);
                                }
                                return false;
                            }
                            all_empty = false;
                            if let Some(gu) = saved {
                                blamed_false.push(gu);
                            }
                            continue;
                        }
                        let snap = self.fork_snapshot();
                        if !self.morphisms(self.meet(&r, a), piece, false).await {
                            all_empty = false;
                            match self.take_blame_on_false(snap, None) {
                                None => return false,
                                Some(gu) => blamed_false.push(gu),
                            }
                            continue;
                        }
                        if let Some(fork) = self.take_fork(snap, None) {
                            forks.push(fork);
                        }
                    }
                    if !all_empty {
                        for gu in blamed_false {
                            self.restore_fork(gu);
                        }
                        return false;
                    }
                    for fork in forks {
                        self.restore_fork(fork);
                    }
                    return true;
                }
                if !forked_atoms.is_empty() {
                    for (a, val, _) in &forked_atoms {
                        st.insert(a.clone(), Some(*val));
                    }
                    if f.restrict(&|a| st.get(a).copied().flatten())
                        .settle()
                        .is_leaf()
                        == Some(false)
                    {
                        for (_, _, fork) in forked_atoms {
                            self.restore_fork(fork);
                        }
                        return true;
                    }
                }
                // Complexity tradeoff: a morphism part that neither the meets it forces nor one
                // split into its morphism types decides is counted inhabited and refused by
                // `verdict`. Why: emptiness of Boolean combinations of morphism types is
                // coNP-hard, like that of tuple types, and one split per branch keeps the search
                // polynomial. Trigger: no atom is forced and the split was spent or does not
                // apply. Tests: `l01_23_groups_and_refusals::refusals::each_refusal_names_its_cause`
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

/// What [`Searching::layout`] reads of a box for [`Choices`]: the component and cell of each
/// open tuple type, by its index in the region; for each component, the number of its open
/// cells, whether it has a value in none of them (`other`), its open cells ascending, and the
/// box's values outside them (`rest`).
struct Layout {
    at: Vec<Option<(usize, usize)>>,
    count: Vec<usize>,
    other: Vec<bool>,
    cells: Vec<Vec<usize>>,
    rest: Vec<Type>,
}

impl Layout {
    /// The choices of the layout, `at` giving the component and cell of an atom.
    fn choices<'a>(&'a self, at: &'a dyn Fn(&Row) -> (usize, usize)) -> Choices<'a> {
        Choices {
            at,
            count: &self.count,
            other: &self.other,
            cells: &self.cells,
        }
    }
}

/// The choices of a tuple of a box for [`Searching::one_pass`]: on each component, one of its
/// open cells, which puts the tuple in the tuple types of that cell and in no other tuple type
/// open there, or a value in none of them when the component has one (`other`).
struct Choices<'a> {
    /// The component and cell of each open tuple type.
    at: &'a dyn Fn(&Row) -> (usize, usize),
    /// The number of open cells of each component.
    count: &'a [usize],
    other: &'a [bool],
    /// The open cells of each component, ascending.
    cells: &'a [Vec<usize>],
}

/// One choice on a component: an open cell, or a value in none of them.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Choice {
    Cell(usize),
    Other,
}

/// A part read by [`Choices::read`]: what is known of each node by its id, the decision lists
/// and exclusive ors read for meets, and the least component of a meet read neither way.
struct Read<'p> {
    known: HashMap<u64, Known<'p>>,
    indexes: HashMap<u64, Index>,
    blame: Option<usize>,
}

/// A point of [`Choices::meet`] on a shared component: the component's place among them, its
/// first block or parity in each operand, and its cell (`None` for a value of no cell either
/// operand mentions).
type Point = (usize, usize, usize, Option<usize>);

/// The point [`Choices::meet`] chose on a shared component, without the component's place.
type MeetPoint = (usize, usize, Option<usize>);

/// A first block of a decision list on a component and the cell giving it (`None` for a value
/// of no cell the list mentions), for [`Choices::complete`].
type Block = (usize, Option<usize>);

/// What [`Choices::decide`] knows of a node: whether some choice puts a tuple in it (`sat`) and
/// whether every choice does (`valid`), each `None` when not known, the components its tuple
/// types are open on, in order, and, for a decision list or an exclusive or under any number of
/// `!`, that list or exclusive or and whether the `!` are odd in number.
struct Known<'p> {
    sat: Option<bool>,
    valid: Option<bool>,
    on: std::rc::Rc<[usize]>,
    leaf: Option<(&'p Part<Row>, bool)>,
}

/// A decision list read for [`Choices::meet`]: the value of each block and, last, the default;
/// each component's [`ListComponent`]; and, for the components the other operand is not open
/// on, each component's latest first block (`by_last`, ascending) and its earliest first block
/// of each value (`by_first`, ascending).
struct ListIndex {
    values: Vec<bool>,
    components: HashMap<usize, ListComponent>,
    by_last: Vec<(usize, usize)>,
    by_first: [Vec<(usize, usize)>; 2],
}

/// One component of a decision list: for each cell it mentions, the first block one of whose
/// literals holds of a tuple with that cell (the number of blocks when none does), the same for
/// a value of no cell it mentions (`rest`), and the cells by that block, all and by the block's
/// value, ascending.
struct ListComponent {
    at: HashMap<usize, usize>,
    rest: usize,
    by_block: Vec<(usize, usize)>,
    by_value: [Vec<(usize, usize)>; 2],
}

/// An exclusive or read for [`Choices::meet`]: its constant; for each component, whether each
/// cell it mentions is on an odd number of its tuple types, the even and the odd cells
/// ascending, and the parities a choice on the component gives (bit 0 even, bit 1 odd); the number of
/// components that give both, and the sum of the parity of those that give one.
struct ParityIndex {
    constant: bool,
    components: HashMap<usize, ParityComponent>,
    both: usize,
    ones: bool,
}

struct ParityComponent {
    at: HashMap<usize, bool>,
    by_parity: [Vec<usize>; 2],
    parities: u8,
}

/// A decision list or an exclusive or, read once for every meet it is an operand of.
enum Index {
    List(ListIndex),
    Parity(ParityIndex),
}

/// The blocks of a decision list whose first block a choice of the shared components may make
/// give the list the value wanted, the other components chosen freely: every block after the
/// earliest first block of those components of that value (`low`), and the blocks of that value
/// up to their latest first block (`high`).
struct Goal<'i> {
    values: &'i [bool],
    want: bool,
    low: usize,
    high: usize,
}

impl Goal<'_> {
    fn good(&self, block: usize) -> bool {
        self.low < block || (block <= self.high && self.values[block] == self.want)
    }
}

/// An operand of [`Choices::meet`]: a decision list and the blocks wanted of it, or an exclusive
/// or, the parity wanted of the choices on the shared components (`None` when either does),
/// and the value wanted of it.
enum Side<'i> {
    List(&'i ListIndex, Goal<'i>),
    Parity(&'i ParityIndex, Option<bool>, bool),
}

/// The choices on one component fixed so far along a decision list: the cell taken, whether
/// two cells were taken, and the cells refused.
#[derive(Default)]
struct Pick {
    taken: Option<usize>,
    clash: bool,
    refused: HashSet<usize>,
}

/// The choices fixed so far along a decision list, by component, and the number of components
/// left with no choice.
#[derive(Default)]
struct Picks {
    on: HashMap<usize, Pick>,
    stuck: usize,
}

impl Choices<'_> {
    /// Whether some choice on each component puts a tuple in `f`: `None` when not known. Each
    /// node is read once, from a stack, keyed by its id:
    /// - a decision list by [`Choices::list`], and an exclusive or in its one form by
    ///   [`Choices::parity`], each exactly;
    /// - `!p` some choice is in exactly when not every choice is in `p`;
    /// - `p | q` some choice is in exactly when one is in `p` or in `q`, and `p & q` every choice
    ///   is in exactly when every one is in both;
    /// - `p & q` some choice is in, and `p | q` every choice is in, read off `p` and `q` when
    ///   they are open on no component in common: the choices on their components are then
    ///   made apart;
    /// - else, when `p` and `q` are each a decision list or an exclusive or under any number
    ///   of `!`, by [`Choices::meet`] on the components they share (step EMPTY-overlap-fast).
    ///
    /// `Err` names the least component shared by the operands of an `&` or `|` read neither
    /// way.
    fn decide(&self, f: &Part<Row>) -> Result<bool, usize> {
        let read = self.read(f);
        read.known[&f.id()].sat.ok_or_else(|| {
            read.blame
                .expect("an unknown node has a meet read neither way")
        })
    }

    /// A choice on each component that puts a tuple in `f`, as [`Choices::decide`] decides it:
    /// `Ok(None)` when there is none, and `Err` as `decide` gives it. The choice is read back
    /// from the root ([`Choices::extract`]) and checked against `f`; components no node needs
    /// are chosen at a value of no open cell, else at their first open cell.
    fn witness(&self, f: &Part<Row>) -> Result<Option<Vec<Option<Choice>>>, usize> {
        let mut read = self.read(f);
        match read.known[&f.id()].sat {
            None => Err(read
                .blame
                .expect("an unknown node has a meet read neither way")),
            Some(false) => Ok(None),
            Some(true) => {
                let mut picks = vec![None; self.count.len()];
                self.extract(f, &read.known, &mut read.indexes, &mut picks);
                for (j, pick) in picks.iter_mut().enumerate() {
                    if pick.is_none()
                        && let Some(&c) = self.cells[j].first()
                    {
                        *pick = Some(if self.other[j] {
                            Choice::Other
                        } else {
                            Choice::Cell(c)
                        });
                    }
                }
                let holds = |a: &Row| {
                    let (j, c) = (self.at)(a);
                    picks[j] == Some(Choice::Cell(c))
                };
                assert!(
                    f.eval(&holds),
                    "the choice read back from the pass is in the part"
                );
                Ok(Some(picks))
            }
        }
    }

    /// Each node of `f` read once, as [`Choices::decide`] says, with the decision lists and
    /// exclusive ors read for meets and the least component of a meet read neither way.
    fn read<'p>(&self, f: &'p Part<Row>) -> Read<'p> {
        let mut known: HashMap<u64, Known<'p>> = HashMap::new();
        let mut indexes: HashMap<u64, Index> = HashMap::new();
        let mut blame: Option<usize> = None;
        let mut stack = vec![(f, false)];
        while let Some((p, ready)) = stack.pop() {
            if !ready && known.contains_key(&p.id()) {
                continue;
            }
            // An exclusive or is read from its set of atoms, before `view`, which would make its
            // halves (module `xor` in `bdd.rs`).
            let k = if let Some((atoms, constant)) = p.expr_id().and_then(|_| p.exclusive_or()) {
                Known {
                    leaf: Some((p, false)),
                    ..self.parity(&atoms, constant)
                }
            } else {
                match p.view() {
                    Ok(b) => Known {
                        leaf: Some((p, false)),
                        ..self.list(b)
                    },
                    Err(form) => {
                        let (x, y) = match form {
                            Form::Not(q) => (q, None),
                            Form::Or(a, b) | Form::And(a, b) => (a, Some(b)),
                        };
                        if !ready {
                            stack.push((p, true));
                            stack.push((x, false));
                            stack.extend(y.map(|y| (y, false)));
                            continue;
                        }
                        let x = &known[&x.id()];
                        match (form, y.map(|y| &known[&y.id()])) {
                            (Form::Not(_), _) => Known {
                                sat: x.valid.map(|v| !v),
                                valid: x.sat.map(|v| !v),
                                on: x.on.clone(),
                                leaf: x.leaf.map(|(l, not)| (l, !not)),
                            },
                            (Form::Or(..), Some(y)) => {
                                let apart = apart(&x.on, &y.on);
                                let sat = or3(x.sat, y.sat);
                                let valid = if apart {
                                    or3(x.valid, y.valid)
                                } else if x.valid == Some(true) || y.valid == Some(true) {
                                    Some(true)
                                } else if sat == Some(false) {
                                    Some(false)
                                } else {
                                    // Every choice is in `x | y` when none is in `!x & !y`.
                                    self.pair(x, y, true, &mut indexes, &mut blame).map(|s| !s)
                                };
                                let on = union_on(&x.on, &y.on);
                                Known {
                                    sat,
                                    valid,
                                    on,
                                    leaf: None,
                                }
                            }
                            (_, Some(y)) => {
                                let apart = apart(&x.on, &y.on);
                                let valid = and3(x.valid, y.valid);
                                let sat = if apart {
                                    and3(x.sat, y.sat)
                                } else if x.sat == Some(false) || y.sat == Some(false) {
                                    Some(false)
                                } else if valid == Some(true) {
                                    Some(true)
                                } else {
                                    self.pair(x, y, false, &mut indexes, &mut blame)
                                };
                                let on = union_on(&x.on, &y.on);
                                Known {
                                    sat,
                                    valid,
                                    on,
                                    leaf: None,
                                }
                            }
                            // `y` is `None` only for `Form::Not` (the match on `form` above sets it
                            // from `b` for `Or` and `And`), and the first arm takes `Not`.
                            (_, None) => unreachable!("an `or` and an `and` have two operands"),
                        }
                    }
                }
            };
            known.insert(p.id(), k);
        }
        Read {
            known,
            indexes,
            blame,
        }
    }

    /// Writes into `picks` a choice on the components of `f` under which `f` is `true`, as
    /// `known` says one is, walking down from `f` once: `!p` wants the other value of `p`; an
    /// `|` wanted true and an `&` wanted false want it of one operand that can give it; an `&`
    /// wanted true and an `|` wanted false want it of both, apart when they share no component,
    /// else of the two lists or exclusive ors by [`Choices::pair_picks`], and of neither when
    /// every choice gives it. A decision list or an exclusive or takes a choice on each of its
    /// components ([`Choices::complete`]). Two nodes reached share no component, so each node is
    /// reached at most once and each component chosen once.
    fn extract<'p>(
        &self,
        f: &'p Part<Row>,
        known: &HashMap<u64, Known<'p>>,
        indexes: &mut HashMap<u64, Index>,
        picks: &mut [Option<Choice>],
    ) {
        let mut stack = vec![(f, true)];
        while let Some((p, want)) = stack.pop() {
            let k = &known[&p.id()];
            // An exclusive or is told by its tag, before `view`, which would make its halves.
            let form = if p.expr_id().is_some() && p.is_exclusive_or() {
                None
            } else {
                p.view().err()
            };
            let (x, y, or) = match form {
                None => {
                    let index = indexes.entry(p.id()).or_insert_with(|| self.index(p));
                    let side = match &*index {
                        Index::List(l) => Side::List(l, goal(l, want, &[])),
                        Index::Parity(q) => Side::Parity(q, self.target(q, want, &[]), want),
                    };
                    self.complete(&side, std::iter::empty(), &[], picks);
                    continue;
                }
                Some(Form::Not(q)) => {
                    stack.push((q, !want));
                    continue;
                }
                Some(Form::Or(a, b)) => (a, b, true),
                Some(Form::And(a, b)) => (a, b, false),
            };
            let gives = |q: &Part<Row>| {
                let k = &known[&q.id()];
                if want {
                    k.sat == Some(true)
                } else {
                    k.valid == Some(false)
                }
            };
            if or == want {
                let one = if gives(x) { x } else { y };
                assert!(gives(one), "an operand gives what its `|` or `&` gives");
                stack.push((one, want));
            } else if apart(&known[&x.id()].on, &known[&y.id()].on) {
                stack.push((x, want));
                stack.push((y, want));
            } else if (k.valid == Some(true) && want) || (k.sat == Some(false) && !want) {
                // Every choice gives it.
            } else {
                self.pair_picks(&known[&x.id()], &known[&y.id()], or, indexes, picks);
            }
        }
    }

    /// Whether some choice puts a tuple in both operands, `x` and `y` open on a component in
    /// common, each under one more `!` when `not`, by [`Choices::meet`] when
    /// each is a decision list or an exclusive or under `!`. `None`, with the least shared
    /// component taken into `blame`, when one is not.
    fn pair<'p>(
        &self,
        x: &Known<'p>,
        y: &Known<'p>,
        not: bool,
        indexes: &mut HashMap<u64, Index>,
        blame: &mut Option<usize>,
    ) -> Option<bool> {
        let shared = shared_on(&x.on, &y.on);
        let (Some(lx), Some(ly)) = (x.leaf, y.leaf) else {
            let least = shared[0];
            *blame = Some(blame.map_or(least, |b| b.min(least)));
            return None;
        };
        let ((px, nx), (py, ny)) = ((lx.0, lx.1 ^ not), (ly.0, ly.1 ^ not));
        for p in [px, py] {
            if let Entry::Vacant(e) = indexes.entry(p.id()) {
                e.insert(self.index(p));
            }
        }
        let side = |p: &Part<Row>, not: bool| match &indexes[&p.id()] {
            Index::List(l) => Side::List(l, goal(l, !not, &shared)),
            Index::Parity(q) => Side::Parity(q, self.target(q, !not, &shared), !not),
        };
        Some(self.meet(&side(px, nx), &side(py, ny), &shared).is_some())
    }

    /// For [`Choices::extract`]: writes into `picks` a choice on the components of `x` and `y`
    /// that puts a tuple in both, each under one more `!` when `not`, as [`Choices::pair`] found
    /// one: the points [`Choices::meet`] chose on the shared components, a point of no cell
    /// either mentions taken at such a value, and the other components of each by
    /// [`Choices::complete`].
    fn pair_picks(
        &self,
        x: &Known<'_>,
        y: &Known<'_>,
        not: bool,
        indexes: &mut HashMap<u64, Index>,
        picks: &mut [Option<Choice>],
    ) {
        let shared = shared_on(&x.on, &y.on);
        // `extract` is called only when `f`'s `sat` is `Some(true)`, and goes down only into
        // nodes whose wanted value is known to be had (`!` swaps `sat` and `valid`; the operand
        // picked passes `gives`; apart operands of an `&` true have `and3` `Some(true)`). Here
        // the node is an `&` wanted true or an `|` wanted false, not apart, and not one every
        // choice gives; in `read` its `sat` (`&`) or `valid` (`|`) is then known only from
        // `pair`, which answers `None` when either leaf is missing.
        let (Some(lx), Some(ly)) = (x.leaf, y.leaf) else {
            unreachable!("a meet found inhabited is of two lists or exclusive ors")
        };
        let ((px, nx), (py, ny)) = ((lx.0, lx.1 ^ not), (ly.0, ly.1 ^ not));
        for p in [px, py] {
            if let Entry::Vacant(e) = indexes.entry(p.id()) {
                e.insert(self.index(p));
            }
        }
        let side = |p: &Part<Row>, not: bool| match &indexes[&p.id()] {
            Index::List(l) => Side::List(l, goal(l, !not, &shared)),
            Index::Parity(q) => Side::Parity(q, self.target(q, !not, &shared), !not),
        };
        let (sx, sy) = (side(px, nx), side(py, ny));
        let chosen = (self.meet(&sx, &sy, &shared)).expect("the meet was found inhabited");
        for (&s, &(_, _, cell)) in shared.iter().zip(&chosen) {
            picks[s] = Some(match cell {
                Some(c) => Choice::Cell(c),
                None => self.rest_choice(s, |c| sx.mentions(s, c) || sy.mentions(s, c)),
            });
        }
        self.complete(&sx, chosen.iter().map(|p| p.0), &shared, picks);
        self.complete(&sy, chosen.iter().map(|p| p.1), &shared, picks);
    }

    /// Writes into `picks` a choice on each component of the list or exclusive or `side` outside
    /// `shared` that gives it its wanted value, the choices on `shared` giving the first blocks
    /// or parities `fixed`. A list's value is that of the least first block: when the latest
    /// first block of each free component gives it, each is chosen there; else the free
    /// component whose earliest first block of that value is least, and at most every other's
    /// latest, is chosen at it. An exclusive or's free components are chosen at an even cell
    /// or none, and one that can give both parities is turned odd when the sum needs it. The
    /// caller knows such a choice exists.
    fn complete(
        &self,
        side: &Side<'_>,
        fixed: impl Iterator<Item = usize>,
        shared: &[usize],
        picks: &mut [Option<Choice>],
    ) {
        let free = |j: &usize| shared.binary_search(j).is_err();
        match side {
            Side::List(l, g) => {
                let end = l.values.len() - 1;
                let p = fixed.min().unwrap_or(end);
                let rest = |j: usize, c: &ListComponent| {
                    (self.other[j] || c.at.len() < self.count[j]).then_some((c.rest, None))
                };
                // Each free component's latest first block and earliest of the value wanted,
                // with the cell giving it (`None` for a value of no cell the list mentions).
                let mut ends: Vec<(usize, Block, Option<Block>)> = Vec::new();
                let mut on: Vec<(&usize, &ListComponent)> =
                    l.components.iter().filter(|(j, _)| free(j)).collect();
                on.sort_unstable_by_key(|e| e.0);
                for (&j, c) in on {
                    let &(i, cell) = c.by_block.last().expect("a component of a list has a cell");
                    let latest = rest(j, c).filter(|r| r.0 >= i).unwrap_or((i, Some(cell)));
                    let first = c.by_value[usize::from(g.want)].first();
                    let first = first.map(|&(i, cell)| (i, Some(cell)));
                    let of_rest = rest(j, c).filter(|r| l.values[r.0] == g.want);
                    let earliest = match (first, of_rest) {
                        (Some(a), Some(b)) => Some(if b.0 < a.0 { b } else { a }),
                        (a, b) => a.or(b),
                    };
                    ends.push((j, latest, earliest));
                }
                let high = ends.iter().map(|e| e.1.0).min().unwrap_or(end);
                let mut at: Vec<(usize, Block)> = ends.iter().map(|e| (e.0, e.1)).collect();
                if l.values[p.min(high)] != g.want {
                    let (k, e) = (ends.iter().enumerate())
                        .filter_map(|(k, e)| {
                            e.2.filter(|&(i, _)| i <= high && i < p).map(|e| (k, e))
                        })
                        .min_by_key(|(_, e)| e.0)
                        .expect("a choice gives the list its wanted value");
                    at[k].1 = e;
                }
                for (j, (_, cell)) in at {
                    let c = &l.components[&j];
                    picks[j] = Some(match cell {
                        Some(cell) => Choice::Cell(cell),
                        None => self.rest_choice(j, |d| c.at.contains_key(&d)),
                    });
                }
            }
            Side::Parity(q, _, want) => {
                let mut need = *want ^ q.constant ^ fixed.fold(false, |s, b| s ^ (b == 1));
                let mut flip = None;
                let mut on: Vec<(&usize, &ParityComponent)> =
                    q.components.iter().filter(|(j, _)| free(j)).collect();
                on.sort_unstable_by_key(|e| e.0);
                for (&j, c) in on {
                    let rest = self.other[j] || c.at.len() < self.count[j];
                    let even = match c.by_parity[0].first() {
                        Some(&cell) => Some(Choice::Cell(cell)),
                        None => rest.then(|| self.rest_choice(j, |d| c.at.contains_key(&d))),
                    };
                    let odd = c.by_parity[1].first().map(|&cell| Choice::Cell(cell));
                    match (even, odd) {
                        (Some(e), o) => {
                            picks[j] = Some(e);
                            if let Some(o) = o {
                                flip = Some((j, o));
                            }
                        }
                        (None, Some(o)) => {
                            picks[j] = Some(o);
                            need ^= true;
                        }
                        // `Choices::index` makes a component only where it pushes a cell into
                        // one of its `by_parity` lists, so when `by_parity[0]` is empty
                        // `by_parity[1]` is not and `odd` is `Some`.
                        (None, None) => unreachable!("a component of an exclusive or has a cell"),
                    }
                }
                if need {
                    let (j, o) = flip.expect("a choice gives the exclusive or its wanted value");
                    picks[j] = Some(o);
                }
            }
        }
    }

    /// A choice on component `j` of a value of no cell `mentioned` holds: a value of no open cell
    /// when there is one, else the first open cell not mentioned, found passing over at most
    /// the cells mentioned. The caller knows one exists.
    fn rest_choice(&self, j: usize, mentioned: impl Fn(usize) -> bool) -> Choice {
        if self.other[j] {
            return Choice::Other;
        }
        let c = (self.cells[j].iter().copied())
            .find(|&c| !mentioned(c))
            .expect("a component with a value of no cell mentioned has an open cell left");
        Choice::Cell(c)
    }

    /// The decision list or exclusive or `p` read for [`Choices::meet`], in time linear in it
    /// and the log of its size.
    fn index(&self, p: &Part<Row>) -> Index {
        // An exclusive or's form is made on first read (module `xor`); its atoms need none.
        if (p.expr_id().is_none() || !p.is_exclusive_or())
            && let Ok(b) = p.view()
        {
            return Index::List(self.list_index(b));
        }
        let (atoms, constant) = p
            .exclusive_or()
            .expect("a leaf is a list or an exclusive or");
        let mut components: HashMap<usize, ParityComponent> = HashMap::new();
        let mut odd: HashMap<(usize, usize), bool> = HashMap::new();
        for a in &atoms {
            *odd.entry((self.at)(a)).or_default() ^= true;
        }
        for (&(j, c), &o) in &odd {
            let e = components.entry(j).or_insert_with(|| ParityComponent {
                at: HashMap::new(),
                by_parity: [Vec::new(), Vec::new()],
                parities: 0,
            });
            e.at.insert(c, o);
            e.by_parity[usize::from(o)].push(c);
        }
        let (mut both, mut ones) = (0, false);
        for (&j, e) in &mut components {
            for by in &mut e.by_parity {
                by.sort_unstable();
            }
            let rest = self.other[j] || e.at.len() < self.count[j];
            let [even, odd] = e.by_parity.each_ref().map(|by| !by.is_empty());
            e.parities = u8::from(even || rest) | (u8::from(odd) << 1);
            match e.parities {
                3 => both += 1,
                2 => ones ^= true,
                _ => {}
            }
        }
        Index::Parity(ParityIndex {
            constant,
            components,
            both,
            ones,
        })
    }

    /// A decision list read for [`Choices::meet`]. On a component, a literal that takes a cell
    /// holds of the tuples with that cell, and one that refuses a cell of those with another
    /// cell or a value of none; so the first block one of whose literals holds is, for a cell,
    /// the first block that takes it or refuses another cell, and for a value of no cell the
    /// first block that refuses one. The list's value is that of the least of these first
    /// blocks over the components.
    fn list_index(&self, b: &Bdd<Row>) -> ListIndex {
        /// One component's literals: the first block that takes each cell, and the first two
        /// blocks that refuse a cell, the second refusing another cell than the first.
        #[derive(Default)]
        struct Lits {
            taken: HashMap<usize, usize>,
            refused: HashSet<usize>,
            first: Option<(usize, usize)>,
            second: Option<usize>,
        }
        let l = b.list();
        let end = l.blocks.len();
        let mut values: Vec<bool> = l.blocks.iter().map(|(v, _)| *v).collect();
        values.push(l.tail);
        let mut lits: HashMap<usize, Lits> = HashMap::new();
        for (i, (_, block)) in l.blocks.iter().enumerate() {
            for (a, taken) in block {
                let (j, c) = (self.at)(a);
                let e = lits.entry(j).or_default();
                if *taken {
                    e.taken.entry(c).or_insert(i);
                } else {
                    e.refused.insert(c);
                    match e.first {
                        None => e.first = Some((i, c)),
                        Some((_, d)) if d != c && e.second.is_none() => e.second = Some(i),
                        Some(_) => {}
                    }
                }
            }
        }
        let mut components = HashMap::new();
        let mut by_last = Vec::new();
        let mut by_first: [Vec<(usize, usize)>; 2] = [Vec::new(), Vec::new()];
        for (j, e) in lits {
            let rest = e.first.map_or(end, |(i, _)| i);
            let refused = |c: usize| match e.first {
                Some((i, d)) if d != c => i,
                Some(_) => e.second.unwrap_or(end),
                None => end,
            };
            let at: HashMap<usize, usize> = (e.taken.keys().chain(&e.refused))
                .map(|&c| (c, e.taken.get(&c).copied().unwrap_or(end).min(refused(c))))
                .collect();
            let mut by_block: Vec<(usize, usize)> = at.iter().map(|(&c, &i)| (i, c)).collect();
            by_block.sort_unstable();
            let by_value = [false, true].map(|v| {
                let at_v = by_block.iter().filter(|&&(i, _)| values[i] == v);
                at_v.copied().collect::<Vec<_>>()
            });
            // The first blocks a choice on `j` can give.
            let has_rest = self.other[j] || at.len() < self.count[j];
            let firsts = || {
                by_block
                    .iter()
                    .map(|&(i, _)| i)
                    .chain(has_rest.then_some(rest))
            };
            by_last.push((firsts().max().expect("a component of a list has a cell"), j));
            for (v, by) in by_first.iter_mut().enumerate() {
                if let Some(i) = firsts().filter(|&i| usize::from(values[i]) == v).min() {
                    by.push((i, j));
                }
            }
            let c = ListComponent {
                at,
                rest,
                by_block,
                by_value,
            };
            components.insert(j, c);
        }
        by_last.sort_unstable();
        for by in &mut by_first {
            by.sort_unstable();
        }
        ListIndex {
            values,
            components,
            by_last,
            by_first,
        }
    }

    /// The parity wanted of the choices on the components `shared` for the exclusive or `q` to
    /// be `want`: `None` when a component outside them gives both parities.
    fn target(&self, q: &ParityIndex, want: bool, shared: &[usize]) -> Option<bool> {
        let (mut both, mut ones) = (q.both, q.ones);
        for s in shared {
            match q.components[s].parities {
                3 => both -= 1,
                2 => ones ^= true,
                _ => {}
            }
        }
        (both == 0).then_some(want ^ q.constant ^ ones)
    }

    /// Whether one choice on the components `shared` (ascending) satisfies both operands, each
    /// with its other components chosen freely. Each component gives points, the first block or
    /// parity of each operand for one choice: a cell either operand mentions, a value of no cell
    /// when there is one, and, of the cells only the operand with more cells on it mentions,
    /// those of one block or parity in two points (the latest, and the least wanted, which is
    /// all the choice needs of them). So the points of a component cost the fewer cells; two
    /// lists are decided by a sweep over the first blocks of one ([`lists`]), a list and an
    /// exclusive or likewise ([`list_parity`]), and two exclusive ors by the four sums of two
    /// parities ([`parities`]): O(p log p) for `p` points.
    ///
    /// The choice found is given back as one point `(x, y, cell)` for each shared component in
    /// order, `cell` `None` for a value of no cell either operand mentions.
    fn meet(&self, x: &Side<'_>, y: &Side<'_>, shared: &[usize]) -> Option<Vec<MeetPoint>> {
        let mut points: Vec<Point> = Vec::new();
        for (k, &s) in shared.iter().enumerate() {
            let x_fewer = x.cells(s) <= y.cells(s);
            let (fewer, more) = if x_fewer { (x, y) } else { (y, x) };
            let point = |f: usize, m: usize, cell: Option<usize>| {
                if x_fewer {
                    (k, f, m, cell)
                } else {
                    (k, m, f, cell)
                }
            };
            let mut seen = HashSet::new();
            for (cell, f) in fewer.each(s) {
                seen.insert(cell);
                let m = more.coord(s, cell).unwrap_or_else(|| more.rest(s));
                points.push(point(f, m, Some(cell)));
            }
            let both = seen.iter().filter(|&&c| more.coord(s, c).is_some()).count();
            if more.cells(s) > both {
                for (m, cell) in more.unseen(s, &seen).into_iter().flatten() {
                    points.push(point(fewer.rest(s), m, Some(cell)));
                }
            }
            if self.other[s] || fewer.cells(s) + more.cells(s) - both < self.count[s] {
                points.push(point(fewer.rest(s), more.rest(s), None));
            }
        }
        let chosen = match (x, y) {
            (Side::List(_, gx), Side::List(_, gy)) => lists(&mut points, shared.len(), gx, gy),
            (Side::List(_, gx), Side::Parity(_, ty, _)) => {
                list_parity(&mut points, shared.len(), gx, *ty)
            }
            (Side::Parity(_, tx, _), Side::List(_, gy)) => {
                for p in &mut points {
                    *p = (p.0, p.2, p.1, p.3);
                }
                let chosen = list_parity(&mut points, shared.len(), gy, *tx);
                for p in &mut points {
                    *p = (p.0, p.2, p.1, p.3);
                }
                chosen
            }
            (Side::Parity(_, tx, _), Side::Parity(_, ty, _)) => {
                parities(&points, shared.len(), *tx, *ty)
            }
        }?;
        Some(
            chosen
                .into_iter()
                .map(|i| (points[i].1, points[i].2, points[i].3))
                .collect(),
        )
    }

    /// A decision list read block by block, the choices fixed so far those under which no
    /// literal of an earlier block holds: a block's value is reached when one of its literals
    /// can hold beside them, and the default when every literal can fail. Each literal is
    /// tested and fixed once, in constant expected time.
    fn list(&self, b: &Bdd<Row>) -> Known<'static> {
        let l = b.list();
        let mut on: Vec<usize> = (l.blocks.iter())
            .flat_map(|(_, lits)| lits.iter().map(|(a, _)| (self.at)(a).0))
            .collect();
        on.sort_unstable();
        on.dedup();
        let mut picks = Picks::default();
        let mut reached = [false; 2];
        for (v, lits) in &l.blocks {
            for (a, taken) in lits {
                let (j, c) = (self.at)(a);
                if !reached[usize::from(*v)] && picks.fits(self, j, c, *taken) {
                    reached[usize::from(*v)] = true;
                }
            }
            for (a, taken) in lits {
                let (j, c) = (self.at)(a);
                picks.fix(self, j, c, !taken);
            }
            if picks.stuck > 0 {
                break;
            }
        }
        if picks.stuck == 0 {
            reached[usize::from(l.tail)] = true;
        }
        Known {
            sat: Some(reached[1]),
            valid: Some(!reached[0]),
            on: on.into(),
            leaf: None,
        }
    }

    /// The exclusive or of `atoms` and `constant`: on each component, the number of its tuple
    /// types a choice puts the tuple in is the number of atoms on the cell chosen, so each
    /// component can add an even number, an odd number or both, and the parities the whole can
    /// reach are added component by component.
    fn parity(&self, atoms: &[Row], constant: bool) -> Known<'static> {
        let mut odd: BTreeMap<(usize, usize), bool> = BTreeMap::new();
        for a in atoms {
            *odd.entry((self.at)(a)).or_default() ^= true;
        }
        // For each component: its cells with atoms, and whether one has an even number of them
        // and one an odd number.
        let mut by: BTreeMap<usize, (usize, bool, bool)> = BTreeMap::new();
        for (&(j, _), &o) in &odd {
            let e = by.entry(j).or_default();
            e.0 += 1;
            if o {
                e.2 = true;
            } else {
                e.1 = true;
            }
        }
        // The parities reachable, even and odd.
        let mut sums = [true, false];
        for (&j, &(cells, even, odd)) in &by {
            let even = even || self.other[j] || cells < self.count[j];
            sums = [
                (sums[0] && even) || (sums[1] && odd),
                (sums[1] && even) || (sums[0] && odd),
            ];
        }
        Known {
            sat: Some(sums[usize::from(!constant)]),
            valid: Some(!sums[usize::from(constant)]),
            on: by.into_keys().collect::<Vec<_>>().into(),
            leaf: None,
        }
    }
}

impl Pick {
    /// Whether a choice on the component is left, of `count` open cells and a value in none when
    /// `other`.
    fn fits(&self, count: usize, other: bool) -> bool {
        !self.clash
            && match self.taken {
                Some(c) => !self.refused.contains(&c),
                None => other || self.refused.len() < count,
            }
    }
}

impl Picks {
    /// Whether a choice is left on every component once cell `c` of component `j` is taken, or
    /// refused when not `taken`.
    fn fits(&self, s: &Choices<'_>, j: usize, c: usize, taken: bool) -> bool {
        let none = Pick::default();
        let p = self.on.get(&j).unwrap_or(&none);
        let was = p.fits(s.count[j], s.other[j]);
        if self.stuck > usize::from(!was) {
            return false;
        }
        !p.clash
            && if taken {
                p.taken.is_none_or(|d| d == c) && !p.refused.contains(&c)
            } else {
                match p.taken {
                    Some(d) => d != c && !p.refused.contains(&d),
                    None => {
                        let refused = p.refused.len() + usize::from(!p.refused.contains(&c));
                        s.other[j] || refused < s.count[j]
                    }
                }
            }
    }

    /// Takes cell `c` of component `j`, or refuses it when not `taken`.
    fn fix(&mut self, s: &Choices<'_>, j: usize, c: usize, taken: bool) {
        let p = self.on.entry(j).or_default();
        let was = p.fits(s.count[j], s.other[j]);
        if taken {
            match p.taken {
                None => p.taken = Some(c),
                Some(d) => p.clash |= d != c,
            }
        } else {
            p.refused.insert(c);
        }
        let now = p.fits(s.count[j], s.other[j]);
        self.stuck = self.stuck + usize::from(was && !now) - usize::from(!was && now);
    }
}

/// Whether two sorted lists of components share none.
fn apart(x: &[usize], y: &[usize]) -> bool {
    let (mut i, mut j) = (0, 0);
    while i < x.len() && j < y.len() {
        match x[i].cmp(&y[j]) {
            std::cmp::Ordering::Less => i += 1,
            std::cmp::Ordering::Greater => j += 1,
            std::cmp::Ordering::Equal => return false,
        }
    }
    true
}

/// The union of two sorted lists of components, sorted.
fn union_on(x: &[usize], y: &[usize]) -> std::rc::Rc<[usize]> {
    let mut u: Vec<usize> = x.iter().chain(y).copied().collect();
    u.sort_unstable();
    u.dedup();
    u.into()
}

/// `x | y` of two values that may be unknown.
fn or3(x: Option<bool>, y: Option<bool>) -> Option<bool> {
    match (x, y) {
        (Some(true), _) | (_, Some(true)) => Some(true),
        (Some(false), Some(false)) => Some(false),
        _ => None,
    }
}

/// `x & y` of two values that may be unknown.
fn and3(x: Option<bool>, y: Option<bool>) -> Option<bool> {
    or3(x.map(|v| !v), y.map(|v| !v)).map(|v| !v)
}

/// The components two sorted lists share, ascending, in time linear in the shorter list and
/// the log of the longer.
fn shared_on(x: &[usize], y: &[usize]) -> Vec<usize> {
    let (short, long) = if x.len() <= y.len() { (x, y) } else { (y, x) };
    let shared = short.iter().filter(|j| long.binary_search(j).is_ok());
    shared.copied().collect()
}

/// The blocks of `l` whose first block on the components `shared` makes it `want` ([`Goal`]).
/// The least first block of the other components is one of a component that every other can
/// match or pass: each component's first block can be its earliest of a value, since the
/// latest first block of the others is at least the least latest first block, which is at
/// least that earliest when that component has the least. Each list skips at most the
/// components shared.
fn goal<'i>(l: &'i ListIndex, want: bool, shared: &[usize]) -> Goal<'i> {
    let out = |j: &usize| shared.binary_search(j).is_err();
    let end = l.values.len() - 1;
    let high = l
        .by_last
        .iter()
        .find(|(_, j)| out(j))
        .map_or(end, |&(i, _)| i);
    let low = (l.by_first[usize::from(want)].iter())
        .find(|(_, j)| out(j))
        .map(|&(i, _)| i)
        .filter(|&i| i <= high)
        .unwrap_or(usize::MAX);
    Goal {
        values: &l.values,
        want,
        low,
        high,
    }
}

impl Side<'_> {
    /// The number of cells the operand mentions on component `s`.
    fn cells(&self, s: usize) -> usize {
        match self {
            Side::List(l, _) => l.components[&s].at.len(),
            Side::Parity(q, ..) => q.components[&s].at.len(),
        }
    }

    /// Whether the operand mentions `cell` on component `s`.
    fn mentions(&self, s: usize, cell: usize) -> bool {
        match self {
            Side::List(l, _) => l.components[&s].at.contains_key(&cell),
            Side::Parity(q, ..) => q.components[&s].at.contains_key(&cell),
        }
    }

    /// The first block or parity of the operand on a cell of `s` it mentions.
    fn coord(&self, s: usize, cell: usize) -> Option<usize> {
        match self {
            Side::List(l, _) => l.components[&s].at.get(&cell).copied(),
            Side::Parity(q, ..) => q.components[&s].at.get(&cell).map(|&o| usize::from(o)),
        }
    }

    /// The first block or parity of the operand on a value of `s` of no cell it mentions.
    fn rest(&self, s: usize) -> usize {
        match self {
            Side::List(l, _) => l.components[&s].rest,
            Side::Parity(..) => 0,
        }
    }

    /// The cells the operand mentions on `s`, each with its first block or parity.
    fn each(&self, s: usize) -> Vec<(usize, usize)> {
        match self {
            Side::List(l, _) => l.components[&s].at.iter().map(|(&c, &i)| (c, i)).collect(),
            Side::Parity(q, ..) => {
                let at = q.components[&s].at.iter();
                at.map(|(&c, &o)| (c, usize::from(o))).collect()
            }
        }
    }

    /// Of the cells the operand mentions on `s` and `seen` does not hold, which all meet the
    /// other operand at its `rest`: for a list the latest first block and the least wanted one,
    /// for an exclusive or one cell of each parity, each with its cell. Each is found passing
    /// over at most the cells seen.
    fn unseen(&self, s: usize, seen: &HashSet<usize>) -> [Option<(usize, usize)>; 2] {
        let unseen = |&&(_, cell): &&(usize, usize)| !seen.contains(&cell);
        match self {
            Side::List(l, g) => {
                let c = &l.components[&s];
                let latest = c.by_block.iter().rev().find(unseen).copied();
                let after = c.by_block.partition_point(|&(i, _)| i <= g.low);
                let after = c.by_block[after..].iter().find(unseen).copied();
                let of_value = (c.by_value[usize::from(g.want)].iter())
                    .find(unseen)
                    .copied()
                    .filter(|&(i, _)| g.good(i));
                let least = match (after, of_value) {
                    (Some(a), Some(b)) => Some(a.min(b)),
                    (a, b) => a.or(b),
                };
                [latest, least.filter(|l| latest.is_none_or(|t| t.0 != l.0))]
            }
            Side::Parity(q, ..) => {
                let c = &q.components[&s];
                [0, 1].map(|o| {
                    let cell = c.by_parity[o].iter().find(|cell| !seen.contains(cell));
                    cell.map(|&cell| (o, cell))
                })
            }
        }
    }
}

/// The order the sweeps read points in: `x` descending, then by component, `y` and cell, so
/// the choice they give back depends on the points alone, not on the order they came in.
fn by_x_descending(points: &mut [Point]) {
    points.sort_unstable_by(|p, q| (q.1, p.0, p.2, p.3).cmp(&(p.1, q.0, q.2, q.3)));
}

/// Whether a choice of one point `(component, x, y, cell)` on each of `components` components
/// has least `x` wanted by `gx` and least `y` wanted by `gy`, and if so the index of each
/// component's point. A pair `(p, q)` is the least of a choice when every component has a
/// point at or above it in both, and one point has `x = p` and one `y = q`, on two components
/// or one point `(p, q)`. The points are swept by `x` descending: at each `x = p` wanted, the
/// greatest `q` every component reaches is the least of the components' greatest `y` so far,
/// and the `y = q` wanted is the least wanted `y` so far on another component than the point
/// with `x = p`, which needs `y` at least `q`; the two least from two components are kept. The
/// choice found takes those one or two points and each other component's point of greatest
/// `y` so far. O(p log p) for `p` points.
fn lists(points: &mut [Point], components: usize, gx: &Goal, gy: &Goal) -> Option<Vec<usize>> {
    by_x_descending(points);
    // Each component's greatest `y` so far and its point.
    let mut top: Vec<Option<(usize, usize)>> = vec![None; components];
    let mut tops: BTreeMap<usize, usize> = BTreeMap::new();
    let mut missing = components;
    // Each component's least wanted `y` so far and its point.
    let mut least = vec![(usize::MAX, usize::MAX); components];
    // The two least wanted `y` so far, on two components.
    let mut best = [(usize::MAX, usize::MAX); 2];
    // Every component at its point of greatest `y`, but those of `fixed`.
    let choose = |top: &[Option<(usize, usize)>], fixed: &[(usize, usize)]| {
        let mut chosen: Vec<usize> = (top.iter())
            .map(|t| t.expect("every component has a point").1)
            .collect();
        for &(k, n) in fixed {
            chosen[k] = n;
        }
        chosen
    };
    let mut i = 0;
    while i < points.len() {
        let x = points[i].1;
        let end = i + points[i..].partition_point(|p| p.1 == x);
        for (n, &(k, _, y, _)) in (i..end).zip(&points[i..end]) {
            if top[k].is_none_or(|t| t.0 < y) {
                match top[k] {
                    None => missing -= 1,
                    Some((t, _)) => {
                        let c = tops.get_mut(&t).expect("a component's top is counted");
                        *c -= 1;
                        if *c == 0 {
                            tops.remove(&t);
                        }
                    }
                }
                top[k] = Some((y, n));
                *tops.entry(y).or_default() += 1;
            }
            if gy.good(y) && y < least[k].0 {
                least[k] = (y, n);
                if best[0].1 == k {
                    best[0].0 = y;
                } else {
                    if best[1].1 == k || y < best[1].0 {
                        best[1] = (y, k);
                    }
                    if best[1].0 < best[0].0 {
                        best.swap(0, 1);
                    }
                }
            }
        }
        if gx.good(x) && missing == 0 {
            let reach = *tops.keys().next().expect("every component has a point");
            // The points with `x` here, by `y` and component descending.
            let mut here: Vec<(usize, usize, usize)> = Vec::new();
            for (n, &(k, _, y, _)) in (i..end).zip(&points[i..end]) {
                if gy.good(y) && y <= reach {
                    return Some(choose(&top, &[(k, n)]));
                }
                here.push((y, k, n));
            }
            here.sort_by_key(|a| std::cmp::Reverse((a.0, a.1)));
            let second = here.iter().find(|p| p.1 != here[0].1);
            for &(y, k, n) in here.first().into_iter().chain(second) {
                let (q, other) = if best[0].1 == k { best[1] } else { best[0] };
                if q <= reach.min(y) {
                    return Some(choose(&top, &[(k, n), (other, least[other].1)]));
                }
            }
        }
        i = end;
    }
    None
}

/// Whether a choice of one point `(component, x, parity, cell)` on each of `components`
/// components has least `x` wanted by `gx` and parities summing to `target` (any, when
/// `None`), and if so the index of each component's point. Swept by `x` descending as
/// [`lists`], with the parities each component reaches so far and their sum over the
/// components: at each `x = p` wanted, each point with `x = p` is tried with its component's
/// part of the sum taken out. The choice found takes that point, an even point of each other
/// component that has one and else an odd one, and turns one that has both odd when the sum
/// needs it. O(p log p) for `p` points.
fn list_parity(
    points: &mut [Point],
    components: usize,
    gx: &Goal,
    target: Option<bool>,
) -> Option<Vec<usize>> {
    by_x_descending(points);
    // Bit 0 even and bit 1 odd: the parities of each component's points so far, a point of
    // each, the number of components with none and with both, and the sum of those with one.
    let mut parities = vec![0u8; components];
    let mut at = vec![[usize::MAX; 2]; components];
    let (mut missing, mut both, mut ones) = (components, 0, false);
    let mut i = 0;
    while i < points.len() {
        let x = points[i].1;
        let end = i + points[i..].partition_point(|p| p.1 == x);
        for (n, &(k, _, g, _)) in (i..end).zip(&points[i..end]) {
            let (was, now) = (parities[k], parities[k] | (1 << g));
            match was {
                0 if now != 0 => missing -= 1,
                1 | 2 if now == 3 => ones ^= was == 2,
                _ => {}
            }
            match (was, now) {
                (0, 2) => ones ^= true,
                (1 | 2, 3) => both += 1,
                _ => {}
            }
            parities[k] = now;
            if at[k][g] == usize::MAX {
                at[k][g] = n;
            }
        }
        if gx.good(x) && missing == 0 {
            for (n, &(k, _, g, _)) in (i..end).zip(&points[i..end]) {
                let p = parities[k];
                let others_both = both - usize::from(p == 3);
                let others = ones ^ (p == 2);
                if others_both > 0 || target.is_none_or(|z| others ^ (g == 1) == z) {
                    let mut chosen = vec![n; components];
                    let (mut sum, mut flip) = (g == 1, None);
                    for (j, (&p, at)) in parities.iter().zip(&at).enumerate() {
                        if j == k {
                            continue;
                        }
                        let even = p & 1 == 1;
                        chosen[j] = at[usize::from(!even)];
                        sum ^= !even;
                        if p == 3 {
                            flip = Some(j);
                        }
                    }
                    if target.is_some_and(|z| z != sum) {
                        let j = flip.expect("a component with both parities turns the sum");
                        chosen[j] = at[j][1];
                    }
                    return Some(chosen);
                }
            }
        }
        i = end;
    }
    None
}

/// Whether a choice of one point `(component, x, y, cell)` of parities on each of
/// `components` components sums to `tx` in `x` and `ty` in `y` (any, when `None`), and if so
/// the index of each component's point: the sums reachable, a set of the four pairs, added
/// component by component, then read back from the last component to the first. O(p) for
/// `p` points.
fn parities(
    points: &[Point],
    components: usize,
    tx: Option<bool>,
    ty: Option<bool>,
) -> Option<Vec<usize>> {
    // Each component's point of each pair of parities, the one of least cell.
    let mut pairs = vec![[usize::MAX; 4]; components];
    for (n, &(k, x, y, cell)) in points.iter().enumerate() {
        let e = &mut pairs[k][2 * x + y];
        if *e == usize::MAX || cell < points[*e].3 {
            *e = n;
        }
    }
    // The sums reachable by the components before each.
    let mut reach = vec![1u8; components + 1];
    for (k, p) in pairs.iter().enumerate() {
        let mut next = 0;
        for a in (0..4).filter(|&a| p[a] != usize::MAX) {
            for r in (0..4).filter(|r| reach[k] >> r & 1 == 1) {
                next |= 1 << (a ^ r);
            }
        }
        reach[k + 1] = next;
    }
    let mut r = (0..4).find(|r| {
        reach[components] >> r & 1 == 1
            && tx.is_none_or(|t| (r >> 1 == 1) == t)
            && ty.is_none_or(|t| (r & 1 == 1) == t)
    })?;
    let mut chosen = vec![0; components];
    for k in (0..components).rev() {
        let a = (0..4)
            .find(|&a| pairs[k][a] != usize::MAX && reach[k] >> (a ^ r) & 1 == 1)
            .expect("a sum reached has a part from each component");
        chosen[k] = pairs[k][a];
        r ^= a;
    }
    Some(chosen)
}

/// A node of a tuple part as [`read_two_sat`] meets it: a part or a diagram.
#[derive(Clone, Copy)]
enum At<'p> {
    Part(&'p Part<Row>),
    Bdd(&'p Bdd<Row>),
}

impl At<'_> {
    /// The key of the node read as itself (`pos`) or as its complement: its id and `pos`.
    fn key(self, pos: bool) -> (u64, bool) {
        match self {
            At::Part(p) => (p.id(), pos),
            At::Bdd(b) => (b.id(), pos),
        }
    }
}

/// An operand of a connective in [`Shape`]: a literal, or a node read as itself or as its
/// complement.
///
/// A node operand is never a leaf, so `read_two_sat` reads `Shape::Leaf` only at the root.
/// Proof. `shape` makes node operands in two places. (1) A diagram node's branch, which the arm
/// order in `shape` uses as an operand only when `leaf` gave it `None`, so it is not a leaf.
/// (2) An operand of an expression `Form::Or(a, b)` or `Form::And(a, b)`, and `Form::Not` of
/// an expression is read through to that expression. bdd.rs makes every expression in its
/// `mod build`, whose `Part::expr` is private (a compiler check): `Part::connect` folds a leaf
/// operand away, `Part::not_expr` makes no `Or` or `And`, and `Part::of_form` takes only a
/// form an expression already had (`Source::Form`), so its operands are no leaves by the same
/// rule. See `Form` in bdd.rs.
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
/// literal `literal` gives it; `None` for an atom it gives none. A diagram node has a leaf on
/// one branch, so it reads as a literal, or as the literal met with or joined to the other branch.
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
                    // Never met: `branch` of a list is `Bdd::view`, which gives the leaf of the
                    // first block's value on the side where its literal holds, so one branch is
                    // always a leaf. (A node with two inner branches was read as the union of
                    // its two arms, `atom & hi | !atom & lo`; that reading is removed.)
                    (None, None) => unreachable!("a diagram node has a leaf branch"),
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
                // The operands of the `or` and of the `or`s under it. No operand is a leaf
                // (proof at `Operand`), so each `or` gives at least two literals and `out`
                // never ends with fewer than two.
                let (mut out, mut under) = (Vec::new(), vec![x, y]);
                while let Some(d) = under.pop() {
                    let l = match d {
                        Operand::Literal(l) => l,
                        Operand::Node(at, pos) => match shape(at, pos, literal)? {
                            Shape::Leaf(_) => unreachable!("an operand is not a leaf"),
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
                match out[..] {
                    [] | [_] => unreachable!("an `or` of two operands gives two literals"),
                    [a, b] => s.clauses.push((a, b)),
                    _ => return None,
                }
            }
        }
    }
    while let Some((g, x)) = forces.pop() {
        let l = match x {
            Operand::Literal(l) => l,
            Operand::Node(at, pos) => match shape(at, pos, literal)? {
                Shape::Leaf(_) => unreachable!("an operand is not a leaf"),
                Shape::Literal(l) => l,
                Shape::And(x, y) => s.meet(at.key(pos), [x, y], &mut forces),
                Shape::Or(..) => return None,
            },
        };
        s.clauses.push((g ^ 1, l));
    }
    Some(s)
}

// The methods of [`TwoSat`] that read [`Operand`] stay here with it; the rest are in `shared.rs`.
impl TwoSat {
    /// Clauses no value holds: a fresh variable both true and false.
    fn contradiction(&mut self) {
        let g = self.fresh();
        self.clauses.extend([(g, g), (g ^ 1, g ^ 1)]);
    }

    /// The variable of the meet with the key `key` and operands `xs`, made the first time, with
    /// each operand put on `forces`.
    fn meet<'p>(
        &mut self,
        key: (u64, bool),
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
}

/// A class of cells on one component: the union of its cells, and its open tuple types.
type Class = (Type, BTreeSet<usize>);

/// Whether `f` holds no tuple on `g` because on some component where every tuple type of `open`
/// is open, their cells fall into two or more disjoint classes ([`overlaps`]) and `f` simplifies
/// to `false` both outside all classes and within each class alone.
// Complexity tradeoff (COMPLEXITY.md K102): the naive test restricts `f` to each of the g
// classes alone, g restrictions of the whole of `f` per component; halving the classes
// restricts the half left over each step, so a restriction at depth d reads what is left of
// `f` after d halvings, and a half that is already `false` is not split further. Both are
// O(g) restrictions of up to |f| nodes in the worst case, O(g |f|) time per component and
// O(m g |f|) over m components, with the classes from `overlaps` (K36). It runs only for a
// search with `blame`, before the Fork refusal it may replace. Given up: no better bound.
fn empty_by_classes(g: &Region, f: &Part<Row>, open: &[usize]) -> bool {
    if f.eval3(&|_| Some(false)) != Some(false) {
        return false;
    }
    let open_set: BTreeSet<usize> = open.iter().copied().collect();
    (0..g.r.len()).any(|j| {
        if g.opens[j] < open.len() || open.iter().any(|&k| !g.is_open(k, j)) {
            return false;
        }
        let cells: Vec<usize> = g.open_cells(j, open).into_iter().collect();
        let groups = overlaps(cells.iter().map(|&c| &g.cells[j][c].ty));
        if groups.len() < 2 {
            return false;
        }
        let mut class_of = BTreeMap::new();
        for (i, is) in groups.iter().enumerate() {
            for &idx in is {
                for &k in &g.cells[j][cells[idx]].rows {
                    if open_set.contains(&k) {
                        class_of.insert(k, i);
                    }
                }
            }
        }
        let at = |a: &Row| class_of.get(&g.index[a]).copied();
        if f.restrict(&|a| at(a).map(|_| false)).is_leaf() != Some(false) {
            return false;
        }
        let mut halves = vec![(f.clone(), 0..groups.len(), None::<Range<usize>>)];
        while let Some((h, this, other)) = halves.pop() {
            let h = match other {
                None => h,
                Some(other) => {
                    let h = h.restrict(&|a| at(a).filter(|i| other.contains(i)).map(|_| false));
                    if h.is_leaf() == Some(false) {
                        continue;
                    }
                    h
                }
            };
            if this.len() == 1 {
                if h.is_leaf() != Some(false) {
                    return false;
                }
                continue;
            }
            let m = this.start + this.len() / 2;
            let (lo, hi) = (this.start..m, m..this.end);
            halves.push((h.clone(), hi.clone(), Some(lo.clone())));
            halves.push((h, lo, Some(hi)));
        }
        true
    })
}

/// The first component on which every tuple type of `open` is open and their cells fall into
/// two or more classes, two cells of different classes sharing no value: each class as the
/// union of its cells and its tuple types among `open`, in the order of their first cells.
/// Each tuple type then goes to one piece of the split, as in the split into disjoint pieces,
/// so the pieces below a split hold each tuple type at most once and the nodes stay linear in
/// the tuple types; a tuple type that held the component would go to every piece, and splits
/// in turn on each component would be a search over all of them.
/// When no component falls into two classes and `keys` is set, the first in the same order
/// whose open cells hold only flat keys gives the pieces of [`key_pieces`] instead, with `true`
/// as the last field; a tuple type is then in several pieces, and the caller only narrows
/// each (`Each::Narrow`) or seeks a value in each (`Each::Seek`, in `class_rep`).
// Complexity tradeoff (GROUP-order-classes-outside-cpoly, COMPLEXITY.md K35b): the first
// component that splits, in written order, made the verdict depend on the order of the
// components: on `((#a|#b), (L12|#c))` less five pairs, splitting the first component forked
// and splitting the second decided Empty. Trying every splitting component and keeping a
// decided one costs a factor `m` per split, `m^d` over `d` nested splits. Used: the
// candidate components are taken in an order fixed by their contents, the component type and
// then the sorted types of its open cells (`Type`'s order is by content digest, the same in
// every run), so a permutation of the components picks the same component. Cost: one key per
// candidate, `O(c log c)` for its `c` open cells, and `O(m log m)` comparisons of keys, each
// `O(1)` on different digests; the `overlaps` calls are those of the first-found search, at
// most one per candidate. A tie (two components of equal type and equal open cells) is broken
// by position; it can then only matter when those two components carry different rows.
fn classes(g: &Region, open: &[usize], keys: bool) -> Option<(usize, Vec<Class>, bool)> {
    let mut order: Vec<(&Type, Vec<&Type>, usize, Vec<usize>)> = (0..g.r.len())
        .filter(|&j| g.opens[j] >= open.len() && open.iter().all(|&k| g.is_open(k, j)))
        .map(|j| {
            let cells: Vec<usize> = g.open_cells(j, open).into_iter().collect();
            let mut tys: Vec<&Type> = cells.iter().map(|&c| &g.cells[j][c].ty).collect();
            tys.sort_unstable();
            (&g.r[j], tys, j, cells)
        })
        .collect();
    order.sort_unstable_by(|a, b| (a.0, &a.1, a.2).cmp(&(b.0, &b.1, b.2)));
    let open: BTreeSet<usize> = open.iter().copied().collect();
    let by_class = order.iter().find_map(|(_, _, j, cells)| {
        let j = *j;
        let groups = overlaps(cells.iter().map(|&c| &g.cells[j][c].ty));
        if groups.len() < 2 {
            return None;
        }
        let classes = groups.into_iter().map(|is| {
            let cells = is.iter().map(|&i| &g.cells[j][cells[i]]);
            let ty = Type::union_all(cells.clone().map(|c| c.ty.clone()));
            let ks = cells
                .flat_map(|c| c.rows.iter().copied())
                .filter(|k| open.contains(k));
            (ty, ks.collect())
        });
        Some((j, classes.collect(), false))
    });
    by_class.or_else(|| {
        let mut order = order.iter().filter(|_| keys);
        order.find_map(|(_, _, j, cells)| Some((*j, key_pieces(g, *j, cells, &open)?, true)))
    })
}

/// The pieces that the open cells `cells` of component `j` cut it into, when each holds
/// finitely many booleans, numbers, strings and bare atoms and nothing else ([`flat_keys`]),
/// and they cut it into two or more: one piece for each set of cells that holds some key and
/// no other cell does, the keys held by exactly that set of cells, with the tuple types of
/// `open` of those cells. Each value of the component then lies in one piece or in no cell,
/// and every cell either holds a piece whole or shares no value with it, so a tuple type of
/// `open` is true on component `j` of a piece exactly when it is among the piece's tuple types
/// (the pieces are the regions of the Venn diagram of the cells, here each a finite set of
/// keys). A tuple type may then be among the tuple types of several pieces, which
/// [`Searching::split_classes`] allows for. `None` when a cell has other values, or when the
/// cells cut the component into one piece only.
// Complexity tradeoff (PERF-diagonal-rows-difference, COMPLEXITY.md K128): the classes of
// [`overlaps`] join every cell that shares a key with another, so `n` cells `a | i` sharing
// the atom `a` form one class, and the part was decided after that by one piece per open tuple
// type, each retesting every cell of the box: order `n²` (650M instructions at n 256, 3.7
// times a doubling). Naive Venn regions of `c` cells are `2^c` sets; read through the keys,
// each key lies in one region, so the regions are at most the keys `K` and the tuple types
// listed over all pieces at most `Σ` (keys of a cell): one pass files each key under the set of
// cells holding it, `O(Σ log K)` comparisons of keys, and as many of the sets, compared in
// `O(|s|)` each. The pieces split on through `split_classes`, `O(Σ log K)` restrictions of
// the part in all, and each piece is narrowed once (`Each::Narrow`). Given up: a piece that
// narrowing alone does not prove empty drops the whole split, and the part goes on to the
// steps after it as before (the split into open tuple types, or `Refused(TupleSplit)`), so
// the work of the pieces narrowed before it is spent for nothing, at most the order of that
// split; deciding such a piece in full would split the box in two components at once, which
// DESIGN.md L1.23 refuses (box covers over `#a | #b | #c` stay refused).
fn key_pieces(g: &Region, j: usize, cells: &[usize], open: &BTreeSet<usize>) -> Option<Vec<Class>> {
    let held = Held::default();
    let none = Type::empty();
    let mut holders: BTreeMap<Key, Vec<usize>> = BTreeMap::new();
    for (x, &c) in cells.iter().enumerate() {
        for k in flat_keys(g.cells[j][c].ty.p_held(&held), &none)? {
            holders.entry(k).or_default().push(x);
        }
    }
    let mut regions: BTreeMap<Vec<usize>, Vec<Key>> = BTreeMap::new();
    for (k, xs) in holders {
        regions.entry(xs).or_default().push(k);
    }
    if regions.len() < 2 {
        return None;
    }
    let pieces = regions.into_iter().map(|(xs, keys)| {
        let ty = Type::union_all(keys.iter().map(key_type));
        let ks = (xs.iter())
            .flat_map(|&x| g.cells[j][cells[x]].rows.iter().copied())
            .filter(|k| open.contains(k));
        (ty, ks.collect())
    });
    Some(pieces.collect())
}

/// The values of `p` as keys, sorted, when it holds finitely many booleans, numbers, strings
/// and bare atoms and nothing else; `None` otherwise. Each key is one value.
fn flat_keys(p: &Parts, none: &Type) -> Option<Vec<Key>> {
    if p.atoms.cofinite()
        || !p.tuples.is_default()
        || p.structs
        || p.morphisms.is_leaf() != Some(false)
    {
        return None;
    }
    let lists = [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings];
    if lists.iter().any(|l| l.cofinite) {
        return None;
    }
    let mut keys: Vec<Key> = (0..2u8)
        .filter(|b| p.bools & (1 << b) != 0)
        .map(Key::Bool)
        .collect();
    for (u, l) in lists.into_iter().enumerate() {
        keys.extend(l.values.iter().map(|v| Key::Lit(u, v.clone())));
    }
    for (n, a) in p.atoms.names() {
        if a.payload != *none {
            return None;
        }
        if a.bare {
            keys.push(Key::Atom(n.clone()));
        }
    }
    keys.sort();
    Some(keys)
}

/// What a value of a type can be equal to, at one node of the trie `overlaps` builds: a
/// literal, the bare atom of the node's name, or a whole universe. An atom name and a tuple
/// length label the node below, which holds the keys of the payloads of that name or of the
/// first components of the tuples of that length. Two types with no key in common are disjoint.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Key {
    Bool(u8),
    Lit(usize, Value),
    Atom(std::sync::Arc<str>),
    Len(usize),
    /// The bare atom of the name of the node.
    Bare,
    /// A whole universe: 0 to 4 the literals of `Lits`, 5 the atoms, 6 the tuples, 7 the
    /// structs, 8 the morphisms.
    All(usize),
}

/// The booleans and literals of `p`, as keys in order, when it lists finitely many booleans,
/// numbers and strings and nothing else (`Parts::finite_literals_only`); else `None`.
fn literal_keys(p: &Parts) -> Option<Vec<Key>> {
    if !p.finite_literals_only() {
        return None;
    }
    let bools = (0..2).filter(|b| p.bools & (1 << b) != 0).map(Key::Bool);
    let lits = [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings]
        .into_iter()
        .enumerate()
        .flat_map(|(u, l)| l.values.iter().map(move |v| Key::Lit(u, v.clone())));
    Some(bools.chain(lits).collect())
}

/// The keys of component `c` of the tuples of `p`, when `p` holds tuples only, none of length
/// `c` or less, and at each length a part `false` with no tuple type holding whose tuple types
/// taken toward `true` hold finitely many booleans and literals at component `c`; `None`
/// otherwise. A tuple of such a part lies in a tuple type it takes toward `true`
/// (`Part::taken_toward`), so its component `c` is one of these keys.
fn component_keys(p: &Parts, c: usize, held: &Held) -> Option<Vec<Key>> {
    if p.has_scalars()
        || !p.atoms.is_default()
        || p.structs
        || p.morphisms.is_leaf() != Some(false)
        || p.tuples.rest
    {
        return None;
    }
    let mut keys = Vec::new();
    for (&n, f) in &p.tuples.lens {
        if f.is_leaf() == Some(false) {
            continue;
        }
        if n <= c || f.eval3(&|_| Some(false)) != Some(false) {
            return None;
        }
        let mut seen = DigestSet::default();
        let mut finite = true;
        f.taken_toward(
            true,
            &mut seen,
            &mut |row: &Row| match literal_keys(row[c].p_held(held)) {
                Some(ks) => keys.extend(ks),
                None => finite = false,
            },
        );
        if !finite {
            return None;
        }
    }
    keys.sort();
    keys.dedup();
    Some(keys)
}

/// The pairs `(a, b)`, `a < b`, of the types `ts` by index that are not shown disjoint by
/// their keys: two types in different classes of [`overlaps`] are disjoint, and within a class
/// two types keyed by their literals ([`literal_keys`]) or by one component of their tuples
/// ([`component_keys`]) that share no key are disjoint. A type with no such keys pairs with
/// every type of its class. Per class, the keying that leaves the fewest pairs is used: its
/// literals, or the component, of those of the longest tuple, that does.
// Complexity tradeoff: the classes cost O(S log S) for types of size S (K36); each keying reads
// each type once, one for the literals and one per component, and the pairs are those of each
// key plus each unkeyed type with its class: order `m²` when every type shares a key, the cost
// of testing every pair, and order `m` for `m` types each with keys of its own beside a few
// unkeyed ones (PERF-disjoint-rows-shared-shapes).
fn meeting_pairs(ts: &[&Type]) -> BTreeSet<(usize, usize)> {
    let held = Held::default();
    let mut pairs = BTreeSet::new();
    for class in overlaps(ts.iter().copied()) {
        if class.len() < 2 {
            continue;
        }
        let parts: Vec<&Parts> = class.iter().map(|&i| ts[i].p_held(&held)).collect();
        let longest = (parts.iter())
            .filter_map(|p| p.tuples.lens.keys().next_back().copied())
            .max()
            .unwrap_or(0);
        let keyings = std::iter::once(None).chain((0..longest).map(Some));
        let keyings = keyings.map(|mode| {
            let keys: Vec<Option<Vec<Key>>> = (parts.iter())
                .map(|p| match mode {
                    None => literal_keys(p).map(|mut ks| {
                        ks.sort();
                        ks.dedup();
                        ks
                    }),
                    Some(c) => component_keys(p, c, &held),
                })
                .collect();
            let mut by_key: BTreeMap<&Key, usize> = BTreeMap::new();
            for k in keys.iter().flatten().flatten() {
                *by_key.entry(k).or_default() += 1;
            }
            let wide = keys.iter().filter(|k| k.is_none()).count();
            let count = wide * class.len() + by_key.values().map(|b| b * b).sum::<usize>();
            (count, keys)
        });
        let (_, keys) = keyings
            .min_by_key(|(count, _)| *count)
            .expect("the literals are always one keying");
        let mut by_key: BTreeMap<&Key, Vec<usize>> = BTreeMap::new();
        for (x, ks) in keys.iter().enumerate() {
            match ks {
                Some(ks) => {
                    for k in ks {
                        by_key.entry(k).or_default().push(class[x]);
                    }
                }
                None => {
                    for &y in &class {
                        if y != class[x] {
                            pairs.insert((y.min(class[x]), y.max(class[x])));
                        }
                    }
                }
            }
        }
        for at in by_key.values() {
            for (i, &a) in at.iter().enumerate() {
                for &b in &at[i + 1..] {
                    pairs.insert((a.min(b), a.max(b)));
                }
            }
        }
    }
    pairs
}

/// The type of the one value of a key of [`literal_keys`] or [`flat_keys`].
fn key_type(k: &Key) -> Type {
    let v = match k {
        Key::Bool(b) => Value::Bool(*b == 1),
        Key::Lit(_, v) => v.clone(),
        Key::Atom(n) => return Type::atom(n),
        _ => unreachable!("literal_keys and flat_keys give booleans, literals and atoms only"),
    };
    Type::lit(&v).expect("a boolean or literal has a type of its own")
}

/// The keys `p` lists in universe `u` (0 to 4 the literals of `Lits`, 5 the atoms, 6 the
/// tuples), each with whether `p` holds a value of it, and whether `p` is cofinite there: it
/// then holds every value of each key it does not list. `none` is the empty type.
fn listed(p: &Parts, u: usize, none: &Type) -> (bool, Vec<(Key, bool)>) {
    match u {
        0..5 => {
            let l = [&p.ints, &p.rats, &p.floats, &p.f32s, &p.strings][u];
            let ks = l
                .values
                .iter()
                .map(|v| (Key::Lit(u, v.clone()), !l.cofinite));
            (l.cofinite, ks.collect())
        }
        5 => {
            let ks = p.atoms.names().iter();
            let ks = ks.map(|(n, a)| (Key::Atom(n.clone()), a.bare || a.payload != *none));
            (p.atoms.cofinite(), ks.collect())
        }
        _ => {
            let ks = p.tuples.lens.iter();
            let ks = ks.map(|(&n, f)| (Key::Len(n), f.is_leaf() != Some(false)));
            (p.tuples.rest, ks.collect())
        }
    }
}

/// An edge of the trie `overlaps` builds: an atom name or a tuple length.
#[derive(Clone, PartialEq, Eq, Hash)]
enum Edge {
    Atom(std::sync::Arc<str>),
    Len(usize),
}

/// The trie of keys: node 0 is the whole type; below a node, one node per atom name and per
/// tuple length that a type holds there. Two nodes merged are one node from then on, and so
/// are their children by each edge.
struct Trie {
    /// Each node's children by edge; a merged node's children are its class root's.
    kids: Vec<HashMap<Edge, usize>>,
    /// The union-find of merged nodes.
    same: Vec<usize>,
}

impl Trie {
    /// The trie of one node.
    fn new() -> Trie {
        Trie {
            kids: vec![HashMap::new()],
            same: vec![0],
        }
    }

    fn find(&mut self, x: usize) -> usize {
        root(&mut self.same, x)
    }

    /// A new node of no children, merged with none.
    fn add(&mut self) -> usize {
        let next = self.kids.len();
        self.kids.push(HashMap::new());
        self.same.push(next);
        next
    }

    fn child(&mut self, x: usize, e: Edge) -> usize {
        let x = self.find(x);
        let y = match self.kids[x].get(&e) {
            Some(&y) => y,
            None => {
                let y = self.add();
                self.kids[x].insert(e, y);
                y
            }
        };
        self.find(y)
    }

    /// Makes `x` and `y` one node, and their children by each edge, in turn. The smaller map
    /// of children moves into the larger, so each child moves O(log n) times over all merges.
    fn merge(&mut self, x: usize, y: usize) {
        self.merge_with(x, y, |_, _| {});
    }

    /// [`Trie::merge`], calling `ready` on each of two distinct nodes before they are merged;
    /// `ready` may give a node children, and may not merge nodes.
    fn merge_with(&mut self, x: usize, y: usize, mut ready: impl FnMut(&mut Trie, usize)) {
        let mut todo = vec![(x, y)];
        while let Some((x, y)) = todo.pop() {
            let (x, y) = (self.find(x), self.find(y));
            if x == y {
                continue;
            }
            ready(self, x);
            ready(self, y);
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

/// What one universe lists at a node: the universe, whether the list is cofinite, and its
/// keys, each with whether a value of it is held.
type Listed = (usize, bool, Vec<(Key, bool)>);

/// What a type puts in the trie `overlaps` builds, read from its own parts: the keys it holds
/// at its node, what it lists there in each universe, and its edges below.
#[derive(Default)]
struct Local<'a> {
    points: Vec<Key>,
    lists: Vec<Listed>,
    kids: Vec<Kid<'a>>,
}

/// One edge below a type's node: whether the type holds the bare atom of the name there,
/// whether it holds every value there (every tuple of the length), and the types inside it
/// under the edge, the payloads of the name or the first components of the tuples.
struct Kid<'a> {
    edge: Edge,
    bare: bool,
    whole: bool,
    inside: Vec<&'a Type>,
}

/// What `p` puts at its node of the trie `overlaps` builds, and the edges below.
#[cfg(test)]
fn local<'a>(p: &'a Parts, none: &Type) -> Local<'a> {
    local_dir(p, none, 0)
}

/// Directional `local`: `dir` chooses which spine component nested tuples follow (`0` first, `1` last).
fn local_dir<'a>(p: &'a Parts, none: &Type, dir: usize) -> Local<'a> {
    let mut points: Vec<Key> = (0..2u8)
        .filter(|b| p.bools >> b & 1 == 1)
        .map(Key::Bool)
        .collect();
    if p.structs {
        points.push(Key::All(7));
    }
    if p.morphisms.is_leaf() != Some(false) {
        points.push(Key::All(8));
    }
    let mut kids = Vec::new();
    for (n, a) in p.atoms.names() {
        if !a.bare && a.payload == *none {
            continue;
        }
        let inside = match a.payload != *none {
            true => vec![&a.payload],
            false => Vec::new(),
        };
        kids.push(Kid {
            edge: Edge::Atom(n.clone()),
            bare: a.bare,
            whole: false,
            inside,
        });
    }
    for (&n, f) in &p.tuples.lens {
        if f.is_leaf() == Some(false) {
            continue;
        }
        // Every value of a part `false` outside its tuple types is in one of them.
        let whole = n == 0 || f.eval3(&|_| Some(false)) != Some(false);
        let mut inside = Vec::new();
        if !whole {
            f.atoms(&mut |row: &'a Row| {
                let idx = if dir == 0 { 0 } else { row.len() - 1 };
                inside.push(&row[idx]);
                true
            });
        }
        kids.push(Kid {
            edge: Edge::Len(n),
            bare: false,
            whole,
            inside,
        });
    }
    let mut lists = Vec::with_capacity(7);
    for u in 0..7 {
        let (cofinite, ks) = listed(p, u, none);
        let lits = ks
            .iter()
            .filter(|(k, held)| *held && matches!(k, Key::Lit(..)));
        points.extend(lits.map(|(k, _)| k.clone()));
        lists.push((u, cofinite, ks));
    }
    Local {
        points,
        lists,
        kids,
    }
}

/// The trie that one strongly connected group of types puts below the node of a member, where
/// the types inside a type are its payloads and the first (`dir == 0`) or last (`dir == 1`)
/// components of its tuples (each type reaches every member): one node per class of nodes, as
/// one walk over the members merges them, the members' types met again at another node. The types
/// of groups below this one are leaves, each at its node. It is the same trie from every member,
/// a member's node being its class. What a type lists at a class is cut to what `overlaps` reads
/// of it: the keys that every cofinite list there lists, or, with no cofinite list, the keys held
/// there.
/// A 1-member unmerged group that traverses one edge from node `0` to node `1` (emitting `lists`
/// at node `0` and zero points/wholes) and hands off at node `1` to `next`.
struct UnitStep {
    edge: Edge,
    lists: Vec<Listed>,
    next: Type,
}

/// Summary of `k >= 1` identical 1-edge or 2-edge [`UnitStep`] periods leading to `tail`.
struct RepeatStem {
    e0: Edge,
    l0: Vec<Listed>,
    second: Option<(Edge, Vec<Listed>)>,
    compressed: bool,
    tail: Type,
}

struct Group {
    /// The group's number, from one count per thread.
    id: usize,
    nodes: Vec<GroupNode>,
    /// Whether this group has one member, merges no nodes, has at most one child or lower-group
    /// edge per node, and any lower group it reaches is also a `single_chain` at node `0`.
    single_chain: bool,
    unit_step: Option<UnitStep>,
    repeat_stem: Option<RepeatStem>,
}

/// One node of a [`Group`]: its children by edge, the keys held there, what the universes
/// list there, whether every value under it is held, the types of lower groups placed there,
/// and whether a type holding every value above it shares a value with it
/// ([`Group::set_deep`]).
#[derive(Default)]
struct GroupNode {
    kids: Vec<(Edge, usize)>,
    points: Vec<Key>,
    lists: Vec<Listed>,
    whole: bool,
    below: Vec<Type>,
    deep: bool,
}

impl Group {
    /// Sets each node's `deep`: whether the node, or a node below it in this group or in the
    /// group of a type of a lower group placed at one of them, holds a key, a cofinite list or
    /// every value under it. That is what a type holding every value above the node shares
    /// with it when no other type reaches it. One walk back along the children from the nodes
    /// that hold such a thing themselves, each node once; the lower groups are made before.
    fn set_deep(nodes: &mut [GroupNode], dir: usize) {
        let mut parents: Vec<Vec<usize>> = vec![Vec::new(); nodes.len()];
        for (x, n) in nodes.iter().enumerate() {
            for &(_, c) in &n.kids {
                parents[c].push(x);
            }
        }
        let lower = |t: &Type| {
            let g = GROUPS.with(|ms| ms[dir].borrow().get(t).cloned());
            let (g, c) = g.expect("a lower group is made before the groups above it");
            g.nodes[c].deep
        };
        let mut todo: Vec<usize> = Vec::new();
        for (x, n) in nodes.iter_mut().enumerate() {
            let held = !n.points.is_empty() || n.lists.iter().any(|&(_, cofinite, _)| cofinite);
            if held || n.whole || n.below.iter().any(lower) {
                n.deep = true;
                todo.push(x);
            }
        }
        while let Some(x) = todo.pop() {
            for &p in &parents[x] {
                if !nodes[p].deep {
                    nodes[p].deep = true;
                    todo.push(p);
                }
            }
        }
    }
}

/// The groups of one direction of each type `overlaps` met, with the type's node ([`GROUPS`]).
type GroupsMet = RefCell<ByType<(std::rc::Rc<Group>, usize)>>;

thread_local! {
    /// The directional groups (`dir` in `0..2`) of each type that `overlaps` met inside a type,
    /// and the type's node there, until `Type::forget_emptiness`.
    // Complexity tradeoff: every type met inside the cells of the unit's splits is kept with
    // its directional group (`dir = 0` first spine, `dir = 1` last spine) until the unit ends,
    // `O(their total size)` of memory; clearing per call instead of caching both slots blows up
    // the K35 list bench from `8.1x` to `11.27x` by rebuilding the `n`-node list group `n` times
    // (`O(n^2)`, COMPLEXITY.md K36). Trigger: any split into classes.
    static GROUPS: [GroupsMet; 2] =
        const { [RefCell::new(ByType::new()), RefCell::new(ByType::new())] };
    /// The number of the next [`Group`] made on this thread.
    static GROUP_IDS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The state of the walk of [`group_of`]: per type met, by its number in the order met, the
/// type, its parts read, and its group's number once its walk ends (`usize::MAX` before); the
/// number of groups made; and what reading a type's parts needs.
struct Walked<'a> {
    number: HashMap<&'a Type, usize>,
    types: Vec<&'a Type>,
    locals: Vec<Local<'a>>,
    group: Vec<usize>,
    groups: usize,
    held: &'a Held,
    none: &'a Type,
    dir: usize,
}

impl<'a> Walked<'a> {
    /// Numbers `t`, met for the first time, and reads its parts; returns its number.
    fn visit(&mut self, t: &'a Type) -> usize {
        let v = self.types.len();
        self.number.insert(t, v);
        self.types.push(t);
        self.locals
            .push(local_dir(t.p_held(self.held), self.none, self.dir));
        self.group.push(usize::MAX);
        v
    }

    /// Makes the group `g` of `members`, whose walks have ended, and keeps it for each member:
    /// one walk from a member over the types inside, each member's parts read once, a member
    /// met again merging its two nodes, a type of a group below a leaf at its node.
    fn make(&mut self, members: &[usize], g: usize) {
        let mut trie = Trie::new();
        let first = self.types[members[0]];
        let mut node: HashMap<&'a Type, usize> = HashMap::from([(first, 0)]);
        let mut todo = vec![(0, members[0])];
        let mut points: Vec<(usize, Key)> = Vec::new();
        let mut lists: Vec<(usize, Listed)> = Vec::new();
        let mut wholes: Vec<usize> = Vec::new();
        let mut below: Vec<&'a Type> = Vec::new();
        let mut merged_any = false;
        while let Some((x, m)) = todo.pop() {
            let l = std::mem::take(&mut self.locals[m]);
            points.extend(l.points.into_iter().map(|k| (x, k)));
            lists.extend(l.lists.into_iter().map(|li| (x, li)));
            for kid in l.kids {
                let y = trie.child(x, kid.edge);
                if kid.bare {
                    points.push((y, Key::Bare));
                }
                if kid.whole {
                    wholes.push(y);
                }
                for t in kid.inside {
                    match node.entry(t) {
                        Entry::Occupied(o) => {
                            merged_any = true;
                            trie.merge(*o.get(), y);
                        }
                        Entry::Vacant(e) => {
                            e.insert(y);
                            match self.number.get(t) {
                                Some(&u) if self.group[u] == g => todo.push((y, u)),
                                _ => below.push(t),
                            }
                        }
                    }
                }
            }
        }
        // Each node's class, numbered in order of the classes' roots.
        let roots: Vec<usize> = (0..trie.same.len()).map(|x| trie.find(x)).collect();
        let mut class = vec![usize::MAX; roots.len()];
        let mut count = 0;
        for x in 0..roots.len() {
            if roots[x] == x {
                class[x] = count;
                count += 1;
            }
        }
        let at = |x: usize| class[roots[x]];
        let mut nodes: Vec<GroupNode> = (0..count).map(|_| GroupNode::default()).collect();
        for (x, kids) in trie.kids.iter().enumerate() {
            if roots[x] == x {
                nodes[at(x)].kids = kids.iter().map(|(e, &c)| (e.clone(), at(c))).collect();
            }
        }
        let mut held: Vec<BTreeSet<Key>> = vec![BTreeSet::new(); count];
        for (x, k) in points {
            held[at(x)].insert(k);
        }
        for (n, ks) in nodes.iter_mut().zip(held) {
            n.points = ks.into_iter().collect();
        }
        // Per class and universe: whether a list is cofinite, the keys every cofinite list
        // lists, and the keys held. A cofinite list makes the class share the universe, so
        // the keys held matter only with none.
        #[allow(clippy::type_complexity)]
        let mut cut: BTreeMap<(usize, usize), (Option<BTreeSet<Key>>, BTreeSet<Key>)> =
            BTreeMap::new();
        for (x, (u, cofinite, ks)) in lists {
            let (meet, kept) = cut.entry((at(x), u)).or_default();
            match cofinite {
                true => {
                    let ks: BTreeSet<Key> = ks.into_iter().map(|(k, _)| k).collect();
                    match meet {
                        Some(m) => m.retain(|k| ks.contains(k)),
                        None => *meet = Some(ks),
                    }
                }
                false => kept.extend(ks.into_iter().filter(|&(_, h)| h).map(|(k, _)| k)),
            }
        }
        for ((c, u), (meet, kept)) in cut {
            let (cofinite, ks) = match meet {
                Some(m) => (true, m),
                None if kept.is_empty() => continue,
                None => (false, kept),
            };
            nodes[c]
                .lists
                .push((u, cofinite, ks.into_iter().map(|k| (k, true)).collect()));
        }
        for y in wholes {
            nodes[at(y)].whole = true;
        }
        for &t in &below {
            nodes[at(node[t])].below.push(t.clone());
        }
        let (mut nodes, quot) = quotient(nodes);
        let at = |x: usize| quot[at(x)];
        merged_any |= nodes.len() < count;
        Group::set_deep(&mut nodes, self.dir);
        let single_chain = members.len() == 1
            && !merged_any
            && nodes.iter().all(|n| n.kids.len() + n.below.len() <= 1)
            && below.iter().all(|t| {
                GROUPS.with(|ms| {
                    ms[self.dir]
                        .borrow()
                        .get(t)
                        .is_some_and(|(lg, lc)| lg.single_chain && *lc == 0)
                })
            });
        let unit_step = (members.len() == 1
            && !merged_any
            && nodes.len() == 2
            && nodes[0].points.is_empty()
            && !nodes[0].whole
            && nodes[0].below.is_empty()
            && nodes[0].kids.len() == 1
            && nodes[0].kids[0].1 == 1
            && nodes[1].points.is_empty()
            && nodes[1].lists.is_empty()
            && !nodes[1].whole
            && nodes[1].kids.is_empty()
            && nodes[1].below.len() == 1)
            .then(|| UnitStep {
                edge: nodes[0].kids[0].0.clone(),
                lists: nodes[0].lists.clone(),
                next: nodes[1].below[0].clone(),
            });
        let repeat_stem = unit_step.as_ref().and_then(|u0| {
            GROUPS.with(|ms| {
                let m = ms[self.dir].borrow();
                let (g1, c1) = m.get(&u0.next)?;
                if *c1 != 0 {
                    return None;
                }
                if let Some(u1) = &g1.unit_step
                    && u0.edge == u1.edge
                    && u0.lists == u1.lists
                {
                    let tail = match &g1.repeat_stem {
                        Some(rs)
                            if rs.second.is_none() && rs.e0 == u0.edge && rs.l0 == u0.lists =>
                        {
                            rs.tail.clone()
                        }
                        _ => u1.next.clone(),
                    };
                    return Some(RepeatStem {
                        e0: u0.edge.clone(),
                        l0: u0.lists.clone(),
                        second: None,
                        compressed: true,
                        tail,
                    });
                }
                let u1 = g1.unit_step.as_ref()?;
                if let Some((g2, c2)) = m.get(&u1.next)
                    && *c2 == 0
                    && let Some(rs2) = &g2.repeat_stem
                    && let Some((e1_2, l1_2)) = &rs2.second
                    && rs2.e0 == u0.edge
                    && rs2.l0 == u0.lists
                    && *e1_2 == u1.edge
                    && *l1_2 == u1.lists
                {
                    return Some(RepeatStem {
                        e0: u0.edge.clone(),
                        l0: u0.lists.clone(),
                        second: Some((u1.edge.clone(), u1.lists.clone())),
                        compressed: true,
                        tail: rs2.tail.clone(),
                    });
                }
                Some(RepeatStem {
                    e0: u0.edge.clone(),
                    l0: u0.lists.clone(),
                    second: Some((u1.edge.clone(), u1.lists.clone())),
                    compressed: false,
                    tail: u1.next.clone(),
                })
            })
        });
        let id = GROUP_IDS.with(|n| n.replace(n.get() + 1));
        let group = std::rc::Rc::new(Group {
            id,
            nodes,
            single_chain,
            unit_step,
            repeat_stem,
        });
        GROUPS.with(|ms| {
            let mut m = ms[self.dir].borrow_mut();
            for &v in members {
                let t = self.types[v];
                m.insert(t.clone(), (group.clone(), at(node[t])));
            }
        });
    }
}

/// The nodes of a group's trie with the bisimilar ones merged, and each old node's new number:
/// two nodes are one when they hold the same keys, lists, whole and lower types, and their
/// children by each edge are one. Node 0 stays 0, and the nodes keep the order of their first
/// old node. Placing a type at a node reads the same keys below it at either of two bisimilar
/// nodes, so `joined` gives the same classes; two types that reach one ring at different
/// members (`Even0` and `Even1` of a ring of alike definitions) then meet at one node, and a
/// placement walks the ring's period, not the ring.
// Complexity tradeoff (PERF-group-overlaps-dir1, COMPLEXITY.md K131): without the quotient, a
// ring of n alike definitions has a trie of order n nodes, one set per member, and two types
// placed at two members of it walk it in step, merging node pairs around the whole ring: O(n)
// per call of `joined`, and `overlaps` is called for about n checks of the ring, O(n^2) in all
// (`l01_29_diagnostics::bench::group_site::naming_the_head_group_scales`, T(8n)/T(n) about 34;
// measured: 32,000 binds per direction-1 run at 8,000 definitions). Used: the coarsest stable
// coloring of the trie ([`crate::refine::Refine`], Paige and Tarjan 1987 with Hopcroft's
// smaller-half rule), O((N + K) log N) for N nodes and K children, once per group (each group
// is cached in `GROUPS`), plus O(N log N) comparisons of the nodes' contents in the starting
// sort. Given up: memory for the refinement's arrays, O(N + K), while the group is made.
fn quotient(nodes: Vec<GroupNode>) -> (Vec<GroupNode>, Vec<usize>) {
    let v = nodes.len();
    // The nodes' starting colors: by what they hold, the lower types in their order.
    let below: Vec<Vec<&Type>> = nodes
        .iter()
        .map(|n| {
            let mut b: Vec<&Type> = n.below.iter().collect();
            b.sort();
            b
        })
        .collect();
    let content = |a: usize, b: usize| {
        let (x, y) = (&nodes[a], &nodes[b]);
        x.points
            .cmp(&y.points)
            .then_with(|| x.lists.cmp(&y.lists))
            .then_with(|| x.whole.cmp(&y.whole))
            .then_with(|| below[a].cmp(&below[b]))
    };
    let mut sorted: Vec<usize> = (0..v).collect();
    sorted.sort_by(|&a, &b| content(a, b));
    // Vertices: the nodes, then one per child (a place), colored by its edge.
    let places: Vec<(usize, &Edge, usize)> = nodes
        .iter()
        .enumerate()
        .flat_map(|(u, n)| n.kids.iter().map(move |(e, c)| (u, e, *c)))
        .collect();
    let size = v + places.len();
    let mut color = vec![0; size];
    let mut next = 0;
    for (i, &a) in sorted.iter().enumerate() {
        if i > 0 && content(sorted[i - 1], a).is_ne() {
            next += 1;
        }
        color[a] = next;
    }
    next += usize::from(v > 0);
    // The edges numbered as first met: a color only needs to tell edges apart, since the
    // classes are numbered by their first node below.
    let mut edges: HashMap<&Edge, usize> = HashMap::new();
    for (e, &(_, edge, _)) in places.iter().enumerate() {
        let k = edges.len();
        color[v + e] = next + *edges.entry(edge).or_insert(k);
    }
    next += edges.len();
    // The vertices counted when the class of a vertex refines: a node's places as a child, a
    // place's node.
    let mut start = vec![0; size + 1];
    for (e, &(_, _, c)) in places.iter().enumerate() {
        start[c + 1] += 1;
        start[v + e + 1] = 1;
    }
    for x in 0..size {
        start[x + 1] += start[x];
    }
    let mut adj = vec![0; start[size]];
    let mut cursor = start[..size].to_vec();
    for (e, &(u, _, c)) in places.iter().enumerate() {
        adj[cursor[c]] = v + e;
        cursor[c] += 1;
        adj[cursor[v + e]] = u;
    }
    let mut into = vec![0; size];
    for &w in &adj {
        into[w] += 1;
    }
    let degree = (0..size)
        .map(|x| (start[x + 1] - start[x]).max(into[x]))
        .max()
        .unwrap_or(0);
    let mut refine = crate::refine::Refine::new(color, next, degree);
    refine.run(&start, &adj);
    let color = refine.color;
    // The classes numbered in the order of their first node, so node 0 stays 0.
    let mut class = vec![usize::MAX; size];
    let mut quot = vec![0; v];
    let mut count = 0;
    for x in 0..v {
        if class[color[x]] == usize::MAX {
            class[color[x]] = count;
            count += 1;
        }
        quot[x] = class[color[x]];
    }
    if count == v {
        return (nodes, quot);
    }
    let mut out: Vec<Option<GroupNode>> = (0..count).map(|_| None).collect();
    for (x, mut n) in nodes.into_iter().enumerate() {
        let slot = &mut out[quot[x]];
        if slot.is_none() {
            for (_, c) in &mut n.kids {
                *c = quot[*c];
            }
            *slot = Some(n);
        }
    }
    let out = out
        .into_iter()
        .map(|n| n.expect("each class has a node"))
        .collect();
    (out, quot)
}

impl<'a> zed_graph::Walk for Walked<'a> {
    /// The place of the next type to read: the kid of the type, and the place under the kid.
    type At = (usize, usize);

    /// The next type inside type `v` whose group is not made before this walk, numbered when
    /// met for the first time.
    fn next(&mut self, v: usize, (k, j): &mut (usize, usize)) -> Option<usize> {
        loop {
            let kid = self.locals[v].kids.get(*k)?;
            let Some(&x) = kid.inside.get(*j) else {
                (*k, *j) = (*k + 1, 0);
                continue;
            };
            *j += 1;
            if let Some(&u) = self.number.get(x) {
                return Some(u);
            }
            if !GROUPS.with(|ms| ms[self.dir].borrow().contains_key(x)) {
                return Some(self.visit(x));
            }
        }
    }

    /// Makes the group of `members` and numbers it.
    fn found(&mut self, members: &mut [usize], _from: Option<usize>) {
        // The members last reached first, the order a pop of Tarjan's stack gives, which makes
        // the trie of the group from the member last reached.
        members.reverse();
        for &m in &*members {
            self.group[m] = self.groups;
        }
        self.make(members, self.groups);
        self.groups += 1;
    }
}

/// The group of `t` and its node there ([`Group`]), made with each group below it not yet
/// made, by Tarjan's walk over the types inside ([`zed_graph::Search`]), which reads each
/// type's parts once: a group is made when its walk ends, after the groups below it.
// Complexity tradeoff: the naive form, a search of what each type reaches and is reached by,
// to find the types of its group, is O(T (T + E)) for the T types and E places of types inside
// types met. Tarjan's search is O(T + E), each type's parts read once (`local_dir`), plus the
// making of each group (`Walked::make`). The types are numbered as the walk meets them
// (`Walked::number`), since types have no numbers of their own; the search is the workspace's
// one Tarjan search, which takes nodes numbered as met (GRAPH-lazy-tarjan), in place of a copy
// of it here, at the same cost.
fn group_of(t: &Type, dir: usize) -> (std::rc::Rc<Group>, usize) {
    if let Some(g) = GROUPS.with(|ms| ms[dir].borrow().get(t).cloned()) {
        return g;
    }
    let none = Type::empty();
    let held = Held::default();
    let mut w = Walked {
        number: HashMap::new(),
        types: Vec::new(),
        locals: Vec::new(),
        group: Vec::new(),
        groups: 0,
        held: &held,
        none: &none,
        dir,
    };
    let root = w.visit(t);
    zed_graph::Search::new().run(&mut w, [root]);
    GROUPS
        .with(|ms| ms[dir].borrow().get(t).cloned())
        .expect("the group of `t` is made")
}

/// The groups [`group_of`] would make for `t`, each as its members in the order given to
/// [`Walked::make`], by the walk `group_of` ran before GRAPH-lazy-tarjan (base 37a14617d), kept
/// as the reference its port onto [`zed_graph::Search`] is tested against. Makes no group.
#[cfg(test)]
fn groups_by_old_walk(t: &Type) -> Vec<Vec<Type>> {
    if GROUPS.with(|ms| ms[0].borrow().contains_key(t)) {
        return Vec::new();
    }
    let none = Type::empty();
    let held = Held::default();
    let mut w = Walked {
        number: HashMap::new(),
        types: Vec::new(),
        locals: Vec::new(),
        group: Vec::new(),
        groups: 0,
        held: &held,
        none: &none,
        dir: 0,
    };
    let root = w.visit(t);
    let (mut low, mut open, mut walk) = (vec![root], vec![root], vec![(root, 0, 0)]);
    let mut made = Vec::new();
    while let Some(&(v, k, j)) = walk.last() {
        let top = walk.len() - 1;
        let kids = &w.locals[v].kids;
        if k < kids.len() {
            if j == kids[k].inside.len() {
                walk[top] = (v, k + 1, 0);
                continue;
            }
            let x = kids[k].inside[j];
            walk[top] = (v, k, j + 1);
            match w.number.get(x) {
                Some(&x) => {
                    if w.group[x] == usize::MAX {
                        low[v] = low[v].min(x);
                    }
                }
                None => {
                    if !GROUPS.with(|ms| ms[0].borrow().contains_key(x)) {
                        let u = w.visit(x);
                        low.push(u);
                        open.push(u);
                        walk.push((u, 0, 0));
                    }
                }
            }
            continue;
        }
        walk.pop();
        if let Some(&(u, _, _)) = walk.last() {
            low[u] = low[u].min(low[v]);
        }
        if low[v] == v {
            let mut members = Vec::new();
            while let Some(m) = open.pop() {
                w.group[m] = made.len();
                members.push(w.types[m].clone());
                if m == v {
                    break;
                }
            }
            made.push(members);
        }
    }
    made
}

/// The groups [`group_of`] makes for `t`, each as its members in the order given to
/// [`Walked::make`]; makes them, as `group_of` does.
#[cfg(test)]
fn groups_by_search(t: &Type) -> Vec<Vec<Type>> {
    /// [`Walked`], recording the members of each group after it orders them.
    struct Recorded<'w, 'a> {
        w: &'w mut Walked<'a>,
        made: Vec<Vec<Type>>,
    }
    impl zed_graph::Walk for Recorded<'_, '_> {
        type At = (usize, usize);
        fn next(&mut self, v: usize, at: &mut (usize, usize)) -> Option<usize> {
            self.w.next(v, at)
        }
        fn found(&mut self, members: &mut [usize], from: Option<usize>) {
            self.w.found(members, from);
            let types = &self.w.types;
            self.made
                .push(members.iter().map(|&m| types[m].clone()).collect());
        }
    }
    if GROUPS.with(|ms| ms[0].borrow().contains_key(t)) {
        return Vec::new();
    }
    let none = Type::empty();
    let held = Held::default();
    let mut w = Walked {
        number: HashMap::new(),
        types: Vec::new(),
        locals: Vec::new(),
        group: Vec::new(),
        groups: 0,
        held: &held,
        none: &none,
        dir: 0,
    };
    let root = w.visit(t);
    let mut r = Recorded {
        w: &mut w,
        made: Vec::new(),
    };
    zed_graph::Search::new().run(&mut r, [root]);
    assert!(GROUPS.with(|ms| ms[0].borrow().contains_key(t)));
    r.made
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

/// A state of a list type read by [`affine_lists_empty`]: whether it holds the stop atom, the
/// rest type taken by each integer it names, and the rest type taken by the integers it does
/// not name, with the integers that one excludes; a missing rest type is no list.
struct ListState {
    stop: bool,
    named: BTreeMap<Value, Type>,
    rest: Option<(BTreeSet<Value>, Type)>,
}

/// The integers of `t` as a finite set, or as the complement of one (`true`); none when `t`
/// holds anything but integers.
fn int_set(t: &Type) -> Option<(bool, BTreeSet<Value>)> {
    let p = t.p();
    let lits = [&p.rats, &p.floats, &p.f32s, &p.strings];
    if !p.scalars_only() || p.bools != 0 || lits.iter().any(|l| l.cofinite || !l.values.is_empty())
    {
        return None;
    }
    Some((p.ints.cofinite, p.ints.values.iter().cloned().collect()))
}

/// The stop atom, link atom and rows of a list type whose items are integers: the stop atom
/// when `t` holds it bare, and the part of its link atom's pairs; none when `t` holds anything
/// else, or a stop or link atom other than `names`.
fn list_rows(t: &Type, names: &mut [Option<Arc<str>>; 2]) -> Option<(bool, Part<Row>)> {
    let p = t.p();
    // A list type holds at most two atoms, its stop atom bare and its link atom with a
    // payload, so a type of more names is refused before any is read: this is asked of every
    // root of every search, and a scan of a union of n atoms there made n searches cost n^2
    // (REGRESS-l01_26-overload). A second bare atom or a second link atom also ends or
    // continues a list, so it is refused too: the rows of a second link atom passed over made a
    // meet with lists through it read as empty.
    if p.structs
        || !p.tuples.is_default()
        || !only_atoms(&p)
        || p.atoms.cofinite()
        || p.atoms.names().len() > 2
    {
        return None;
    }
    let (mut stop, mut link) = (None, None);
    for (name, a) in p.atoms.names() {
        match (a.bare, a.payload == Type::empty()) {
            (true, true) if stop.is_none() => stop = Some(name.clone()),
            // Never met: the atoms are finite (tested above), and `Atoms::set`, the one writer
            // of `names` (module `types::atoms`), keeps no name whose part is `AtomPart::none()`
            // there.
            (false, true) => unreachable!("a finite atoms map lists a name with no part"),
            (false, false) if link.is_none() => link = Some((name.clone(), a.payload.clone())),
            _ => return None,
        }
    }
    let (name, payload) = link?;
    let q = payload.p();
    if q.tuples.rest || q.tuples.lens.len() != 1 || !q.atoms.is_default() || q.structs {
        return None;
    }
    let f = q.tuples.lens.get(&2)?.clone();
    for (known, name) in names.iter_mut().zip([stop.clone(), Some(name)]) {
        match (&*known, name) {
            (_, None) => {}
            (None, name) => *known = name,
            (Some(k), Some(n)) if *k == n => {}
            _ => return None,
        }
    }
    Some((stop.is_some(), f))
}

/// The rows of a list operand read by integer: each integer a finite row names, with its next
/// type, and the cofinite row if any: the finite set of integers it leaves out, and its next type.
type NamedRows = (BTreeMap<Value, Type>, Option<(BTreeSet<Value>, Type)>);

/// Whether a meet of lists of integers is proved empty by the parities of its operands:
/// `Some(true)` when proved empty, else none (the search decides it).
///
/// The class read: `t`'s link atom holds a meet of operands, each a union of rows
/// `link(H, R)` with `H` a set of integers, and every rest type `R` reached from an operand is
/// again such a union. Each operand is then a deterministic automaton over the integers whose
/// states are the rest types. The class takes the operands whose automaton has at most two
/// states and in which each integer usable in every operand swaps the two states or keeps
/// them; a state of an operand is accepting when it holds the stop atom. Then the state of
/// each operand after a list is its first state plus, over GF(2), the number of items of each
/// integer that swaps it: an affine system (Schaefer 1978, Theorem 2.1(e)). A usable integer
/// that swaps at most two of the operands that constrain the end (one accepting state of
/// two) is an edge between them, or to a ground node when it swaps one; a list ends accepted
/// by all exactly when, in each connected part of this graph without the ground node, an even
/// number of operands must change state (the column space of a graph's incidence matrix over
/// GF(2)). A list of length at least one exists when that holds and some integer is usable;
/// the empty list exactly when `t` holds the stop atom.
// Complexity tradeoff: the meet of k two-state lists is decided as a linear system over
// GF(2) by union-find over the operands, O(s log s) in the size s of the rows read, where the
// search walks their product, 2^k states, and refuses it as a fork (`narrow_tuples`). Naive
// version: dense Gaussian elimination, O(L k min(L, k)) for L integers and k operands, cubic.
// Given up: a usable integer that swaps three or more constraining operands, an operand of
// three or more states, a nondeterministic operand, or an integer that keeps one state and
// leaves the other; each goes to the search as before. Test:
// `l01_23_subtyping::setop::a_parity_meet_with_a_second_link_atom_is_inhabited`.
fn affine_lists_empty(t: &Type) -> Option<bool> {
    let mut names = [None, None];
    let (root_stop, f) = list_rows(t, &mut names)?;
    if root_stop {
        return None;
    }
    // The operands: the conjuncts of the meet, each once.
    // A list met with rows holds one operand per row met, and one for the rows it joins.
    let mut conjuncts: Vec<Vec<Row>> = Vec::new();
    let (mut seen, mut stack) = (HashSet::new(), vec![f.clone()]);
    while let Some(p) = stack.pop() {
        if !seen.insert(p.id()) {
            continue;
        }
        match (p.view(), p.meet_rows()) {
            (Err(Form::And(a, b)), _) => {
                stack.push(b.clone());
                stack.push(a.clone());
            }
            (_, Some((met, joined))) => {
                conjuncts.extend(met.into_iter().map(|r| vec![r]));
                conjuncts.extend(joined);
            }
            _ => conjuncts.push(p.union_rows()?),
        }
    }
    if conjuncts.len() < 2 {
        return None;
    }
    // Each state read once, by its type; local to this call.
    let mut states: Vec<ListState> = Vec::new();
    let mut rows_of: Vec<Vec<Row>> = Vec::new();
    let mut number: ByType<usize> = ByType::default();
    let read_rows = |rows: &[Row]| -> Option<NamedRows> {
        let mut named = BTreeMap::new();
        let mut rest: Option<(BTreeSet<Value>, Type)> = None;
        for row in rows {
            let (cofinite, values) = int_set(&row[0])?;
            if cofinite {
                if rest.is_some() {
                    return None;
                }
                rest = Some((values, row[1].clone()));
            } else {
                for v in values {
                    if named.insert(v, row[1].clone()).is_some() {
                        return None;
                    }
                }
            }
        }
        if let Some((out, _)) = &rest
            && named.keys().any(|v| !out.contains(v))
        {
            return None;
        }
        Some((named, rest))
    };
    // Per operand: its states (one or two) by number, its first state, and its accepting ones.
    let mut operands: Vec<(Vec<usize>, usize)> = Vec::new();
    for c in &conjuncts {
        let mut first_rows = c.clone();
        first_rows.sort();
        first_rows.dedup();
        let mut own: Vec<usize> = Vec::new();
        let mut todo: Vec<Type> = first_rows.iter().map(|r| r[1].clone()).collect();
        while let Some(x) = todo.pop() {
            let i = match number.get(&x) {
                Some(&i) => i,
                None => {
                    let (stop, g) = list_rows(&x, &mut names)?;
                    let mut rows = g.union_rows()?;
                    rows.sort();
                    rows.dedup();
                    let (named, rest) = read_rows(&rows)?;
                    let i = states.len();
                    states.push(ListState { stop, named, rest });
                    rows_of.push(rows);
                    number.insert(x.clone(), i);
                    i
                }
            };
            if own.contains(&i) {
                continue;
            }
            own.push(i);
            if own.len() > 2 {
                return None;
            }
            let st = &states[i];
            todo.extend(st.named.values().cloned());
            todo.extend(st.rest.iter().map(|(_, r)| r.clone()));
        }
        // The first state is the state whose rows are the operand's: the two agree on every
        // list of length one or more, and the empty list is read off `t` itself.
        let start = *own.iter().find(|&&i| rows_of[i] == first_rows)?;
        own.sort();
        operands.push((own, start));
    }
    // The action of an integer on an operand: 0 dead in every state, 1 keeps, 2 swaps, and 3
    // anything else.
    fn step<'a>(st: &'a ListState, v: Option<&Value>) -> Option<&'a Type> {
        match v.and_then(|v| st.named.get(v)) {
            Some(r) => Some(r),
            None => match &st.rest {
                Some((out, r)) if v.is_none_or(|v| !out.contains(v)) => Some(r),
                _ => None,
            },
        }
    }
    let act = |own: &[usize], v: Option<&Value>| -> u8 {
        let to = |i: usize| step(&states[i], v).map(|r| number[r]);
        match own {
            [x] => match to(*x) {
                None => 0,
                Some(y) if y == *x => 1,
                Some(_) => 3,
            },
            [x, y] => match (to(*x), to(*y)) {
                (None, None) => 0,
                (Some(a), Some(b)) if a == *x && b == *y => 1,
                (Some(a), Some(b)) if a == *y && b == *x => 2,
                _ => 3,
            },
            _ => 3,
        }
    };
    // Per operand: whether it constrains the end, and the change it needs (first state to the
    // accepting one).
    let mut need: Vec<Option<bool>> = Vec::with_capacity(operands.len());
    for (own, start) in &operands {
        let accepting: Vec<usize> = own.iter().copied().filter(|&i| states[i].stop).collect();
        match accepting[..] {
            [] => return Some(true),
            [a] if own.len() == 2 => need.push(Some(a != *start)),
            _ => need.push(None),
        }
    }
    // The integers named by some operand, with the operands naming each; the rest act as the
    // operands' unnamed integers do.
    let mut by_value: BTreeMap<&Value, Vec<usize>> = BTreeMap::new();
    for (o, (own, _)) in operands.iter().enumerate() {
        for &i in own {
            let st = &states[i];
            for v in st
                .named
                .keys()
                .chain(st.rest.iter().flat_map(|(out, _)| out.iter()))
            {
                let e = by_value.entry(v).or_default();
                if e.last() != Some(&o) {
                    e.push(o);
                }
            }
        }
    }
    let unnamed: Vec<u8> = operands.iter().map(|(own, _)| act(own, None)).collect();
    let dead_unnamed = unnamed.iter().filter(|&&a| a == 0).count();
    let other_unnamed = unnamed.iter().filter(|&&a| a == 3).count();
    let swaps_unnamed: Vec<usize> = (0..operands.len())
        .filter(|&o| unnamed[o] == 2 && need[o].is_some())
        .collect();
    // Union-find over the constraining operands, the last node the ground.
    let n = operands.len();
    let mut parent: Vec<usize> = (0..=n).collect();
    let mut usable = false;
    let edge = |parent: &mut Vec<usize>, swapped: &[usize]| -> Option<()> {
        match *swapped {
            [] => {}
            [a] => join(parent, a, n),
            [a, b] => join(parent, a, b),
            _ => return None,
        }
        Some(())
    };
    for (v, ops) in &by_value {
        let acts: Vec<u8> = ops.iter().map(|&o| act(&operands[o].0, Some(v))).collect();
        let (mut dead, mut other) = (dead_unnamed, other_unnamed);
        for (&o, &a) in ops.iter().zip(&acts) {
            dead = dead - usize::from(unnamed[o] == 0) + usize::from(a == 0);
            other = other - usize::from(unnamed[o] == 3) + usize::from(a == 3);
        }
        if dead > 0 {
            continue;
        }
        // At most two operands swap, so the operands swapping every unnamed integer are at
        // most two more than those naming `v`; this keeps the step linear in `ops`.
        if other > 0 || swaps_unnamed.len() > ops.len() + 2 {
            return None;
        }
        let mut flips: BTreeSet<usize> = swaps_unnamed.iter().copied().collect();
        for (&o, &a) in ops.iter().zip(&acts) {
            if need[o].is_some() {
                flips.remove(&o);
                if a == 2 {
                    flips.insert(o);
                }
            }
        }
        if flips.len() > 2 {
            return None;
        }
        usable = true;
        let swapped: Vec<usize> = flips.into_iter().collect();
        edge(&mut parent, &swapped)?;
    }
    // The integers no operand names: there are always some.
    if dead_unnamed == 0 {
        if other_unnamed > 0 {
            return None;
        }
        usable = true;
        edge(&mut parent, &swaps_unnamed)?;
    }
    if !usable {
        return Some(true);
    }
    let mut odd: HashMap<usize, bool> = HashMap::new();
    for (o, &d) in need.iter().enumerate() {
        if d == Some(true) {
            *odd.entry(root(&mut parent, o)).or_default() ^= true;
        }
    }
    let ground = root(&mut parent, n);
    odd.iter().any(|(&r, &b)| b && r != ground).then_some(true)
}

/// One step of `overlaps` placing the types inside a type: place a type at a node for a cell,
/// read a node of a placed group at a node, or merge two nodes.
enum Work {
    /// The type at the node, inside the cell's type.
    Place(usize, Type, usize),
    /// The node of a group placed (by placement and group node) at a trie node.
    Bind(usize, usize, usize),
    Merge(usize, usize),
}

/// What `overlaps` has placed: per placement (a group placed for one cell), its group, its cell
/// and the trie node of each group node placed so far; per trie node, the group node placed
/// there and not read yet; and the keys, lists and wholes read, by node and cell.
#[derive(Default)]
struct Placing {
    groups: Vec<std::rc::Rc<Group>>,
    cells: Vec<usize>,
    at: Vec<HashMap<usize, usize>>,
    /// The (placement, group node) placed at a node and not read: each waits until another
    /// type reaches it, by a key, a link or a merge. Such a node has no children, and the
    /// types of lower groups at its group node are not placed yet.
    pending: Vec<Option<(usize, usize)>>,
    points: Vec<(usize, Key, usize)>,
    lists: Vec<(usize, Listed, usize)>,
    wholes: Vec<(usize, usize)>,
    /// Per cell: remaining `Work::Place` + `Work::Bind` items, waiting `pending` nodes, and
    /// lowest `Group::id` placed so far (Tarjan bottom-up topological order).
    active: Vec<usize>,
    pending_cnt: Vec<usize>,
    min_gid: Vec<usize>,
}

impl Placing {
    /// Gives each node of `trie` a state.
    fn sync(&mut self, trie: &Trie) {
        self.pending.resize(trie.kids.len(), None);
    }

    /// Reads what waits at the node `x`, a class root. `x` has no children, so reading it
    /// merges nothing; it places the types of lower groups at it.
    fn reach(&mut self, trie: &mut Trie, x: usize, work: &mut Vec<Work>) {
        if let Some((p, q)) = self.pending[x].take() {
            self.pending_cnt[self.cells[p]] -= 1;
            self.read(trie, x, p, q, work);
        }
    }

    /// Reads the group node `q` of placement `p` at the class root `x`: its keys, lists and
    /// whole for the placement's cell, its children linked, and the types of lower groups at
    /// it to place for that cell. A child whose group node is placed already is that node; a
    /// new child waits.
    fn read(&mut self, trie: &mut Trie, x: usize, p: usize, q: usize, work: &mut Vec<Work>) {
        let Placing {
            groups,
            cells,
            at,
            pending,
            points,
            lists,
            wholes,
            active,
            pending_cnt,
            ..
        } = self;
        let n = &groups[p].nodes[q];
        let i = cells[p];
        points.extend(n.points.iter().map(|k| (x, k.clone(), i)));
        lists.extend(n.lists.iter().map(|li| (x, li.clone(), i)));
        if n.whole {
            wholes.push((x, i));
        }
        for (e, r) in &n.kids {
            match (trie.kids[x].get(e).copied(), at[p].get(r).copied()) {
                (Some(kid), Some(z)) => work.push(Work::Merge(kid, z)),
                (None, Some(z)) => {
                    trie.kids[x].insert(e.clone(), z);
                }
                (Some(kid), None) => {
                    let kid = trie.find(kid);
                    at[p].insert(*r, kid);
                    active[i] += 1;
                    work.push(Work::Bind(kid, p, *r));
                }
                (None, None) => {
                    let v = trie.add();
                    pending.push(Some((p, *r)));
                    pending_cnt[i] += 1;
                    trie.kids[x].insert(e.clone(), v);
                    at[p].insert(*r, v);
                }
            }
        }
        active[i] += n.below.len();
        work.extend(n.below.iter().map(|t| Work::Place(x, t.clone(), i)));
    }
}

/// The types `ts` in classes, by index in order of their first members, joined when they share
/// a key: two types of different classes are disjoint. The keys sit in a trie: the atoms of
/// one name are keyed by their payload's keys under the node of the name, and the tuples of one
/// length by the keys of their first component under the node of the length, so `#a((1,))` and
/// `#a((2,))`, or `(1,)` and `(2,)`, share no key. The classes are then cut by one more run
/// for each later component `c`, in which the tuples longer than `c` are keyed by component
/// `c`, so `(1, 2)` and `(1, 3)` are apart too. A type that holds every value under a node,
/// such as every tuple of a length, shares a key with each type that holds a key under it. At
/// each node, the cofinite types of a universe share it whole. A finite type meets one of them
/// exactly when it holds a key that one does not list, so it shares the whole universe when it
/// holds a key outside those every cofinite type lists; that set is the meet of their lists,
/// taken from the shortest. Each type inside a type is placed once for it, found by its
/// structure, so the classes do not depend on whether equal types are one shared type; met
/// again at another node read, it merges that node with the first. The types inside are placed
/// a strongly connected group at a time ([`Group`]): a group's trie is made once until
/// `Type::forget_emptiness` and placed for each type that reaches it, and read one node at a
/// time ([`Placing`]): a node is read where the type it is placed for meets it first, or where
/// another type reaches it, and the types of lower groups at a node are placed when it is
/// read, so a ring of k types costs each type that reaches it the nodes it shares with other
/// types. The work is the size of the tries read times the log of the keys, and each child of
/// a merged node moves O(log n) times.
// Complexity tradeoff: the keys are coarser than the meet of two types in three cases, each of
// which joins disjoint types: tuples that share a key on every component, each in a different
// tuple type, as `(1, 1) | (2, 2)` and `(1, 2)`; a tuple part of length two or more that is
// not within its tuple types (a negated tuple type outside any other) holds every tuple of its
// length, so it joins every type under that node, and so does one of length one whose first
// components are not read off it (below); and a type met at two nodes inside one type merges
// the two, so `(2,)` and `#e((2,))` are joined beside `(1,) | #e((1,))`. Joined types get the
// later steps of `tuples` on the part whole; where those steps do not decide it, the part
// counts as inhabited for `is_empty`, and `verdict` answers `Refused(TupleSplit)` (a subtyping
// check fails and names the types). The cost of a joined class is that of deciding it whole:
// k pinwheels joined in one class cost order k^2. The naive way keyed tuples by their first
// component only, and placed a tuple part of length one outside its tuple types whole, so k
// pinwheels whose ends share a first component, or with one end every tuple but the other
// ends, fell in one class; a check whose top is a meet, so that `disjoint_disjuncts` does not
// split the union first (the full union a subtype of the one with its middles, the union less
// a box it does not meet), cost from k = 16 to 128 59.7 times the bytes allocated (subtypes,
// one end outside), 57.9 times (one first component), and 49.5 and 47.3 times (less a box,
// full). Here the classes are the common refinement of one run per component `c`: run 0 is
// the trie above; run `c ≥ 1` places only the types that hold a tuple longer than `c`, their
// tuples of those lengths keyed by component `c`, and puts the types that hold anything else,
// or meet a type cofinite in tuples there, in one class with the types outside the run. Two
// types that meet share a value, which every run keys alike, so each run's partition is
// sound, and so is their common refinement. A part of one-tuples is placed at the first
// components it can hold ([`first_components`]): those of the tuple types it takes toward
// `true`, and with those false, those of a meet of tuple types and their complements, so
// `(int,) \ (1,)` is apart from `(1,)`. A part `false` with no tuple type holding places only
// the tuple types it takes toward `true`, not those it refuses on every path. Each tuple type
// is placed once per component, so the runs cost the size of the types, O(S log S) with the
// sort by longest length and the tries. Measured in instructions, with the bytes allocated in
// parentheses: from k = 64 to 512 the subtype checks cost 8.7 times (8.3; one end outside,
// 268.6M to 2,346.7M) and 8.4 times (8.1; one first component, 212.4M to 1,783.8M); from
// k = 16 to 128 the union less a box, full, 7.9 times (7.7; 399.7M to 3,148.3M) and 7.9 times
// (7.9; 351.5M to 2,769.2M); from k = 32 to 256 the empty verdict 8.7 times (8.2; 852.4M to
// 7,395.0M) and 8.0 times (8.0; 688.6M to 5,503.3M). Merged nodes join only types that hold
// one key under them, and k pinwheels whose ends repeat one integer under a tuple and a
// payload stay k classes (4,508M instructions at k = 512, 9.0 times k = 64). Why the three
// cases remain: the meet of two tuple types is an emptiness check in each component, and
// testing it for each pair costs their square and a search each, while one component's keys
// cost the size of the types; a tuple part outside its tuple types meets another type exactly
// when that type is not within the union of the part's negated tuple types, which is itself
// an emptiness check; walking a type inside a type once per node it is met at would unfold a
// shared type, exponential in its nesting. Trigger: cells on the split component whose tuples
// share a key on every component, a negated tuple type of length two or more, or one type
// reached by two paths inside a cell. Tests:
// `types::empty::tests::classes_are_exact_on_cofinite_sets_names_lengths_and_components`
// (`(1, 2)` and `(1, 3)` apart, `(7, 7) | (8, 8)` and `(7, 8)` joined, a type cofinite in
// tuples joined with the pairs it meets),
// `types::empty::tests::classes_join_under_a_tuple_part_outside_its_types_and_merge_the_nodes_of_a_type_met_twice`,
// `types::empty::tests::types_that_meet_are_joined_in_random_unions_and_negations_of_tuples`
// (1,000 random cases against the meets), and in `l01_23_subtyping::scaling`:
// `pinwheels_whose_ends_share_a_first_component_are_decided` and `…_scale`,
// `pinwheels_with_an_end_outside_every_tuple_type_are_decided` and `…_scale` (the verdict
// at k = 32 and 256, the subtype checks at 64 and 512, the union less a box at 16 and 128),
// `pinwheels_whose_ends_repeat_an_integer_agree_with_the_model` and `…_scale` (k = 64 and 512,
// shared and built apart), and `payload_and_one_tuple_pinwheels_scale`. COMPLEXITY.md K36. A
// complete solution needs the connected parts of the graph in which two types meet: for tuples
// that is the intersection graph of boxes, whose edges can number the square of the types, and
// each edge an emptiness check.
// Complexity tradeoff: the naive way places a group's whole trie for each type that reaches
// it, at the node it is met at, with the groups below it: k types that each reach one ring of
// k types with a name each, `T_j = #a_j((T_{j+1},)) | j`, which merges no node, place k tries
// of k nodes, order k^2 in one call (3.8, 16, 58 and 268 ms at k = 64, 128, 256, 512; the walk
// over the ring for each type before groups cost the same), and so does the ring whose members
// each hold a type of a lower group, `T_j = #a_j((T_{j+1},)) | #b_j((int,)) | j` (5.4, 25,
// 102, 393 and 1,554 ms at k = 64 to 1,024, load 13 to 15). Here every group is read lazily
// ([`Placing`]): a node placed and not met by another type waits, and is read when another
// type reaches it, by a key, a link or a merge; the types of lower groups at a node are placed
// for its cell only when it is read, each lower group once per cell (the map `placed`), so a
// lower type met at two nodes read merges them as before. Each type costs the nodes it shares
// with others: O(k log k) for both rings, the second 0.18, 0.35, 0.70, 1.4, 2.8 to 4.1, 6.4 to
// 9.4 and 18 to 34 ms at k = 64 to 4,096 (load 17 to 28; the spread above k = 1,024 is the
// cache), and 77M, 155M, 312M and 630M instructions at k = 512 to 4,096, 2.0 times per
// doubling, fitted exponent 1.0. A type holding every value above a node that waits shares a
// value with the placement's cell when the node is deep ([`Group::set_deep`]: it, or a node
// below it in its group or in a lower group at one of them, holds a key, a cofinite list or
// every value under it), and enters its placement once, passing to the nodes read, since a
// node with children holds a member and so reaches every node of the group. The tradeoff: the
// classes are finer than placing whole, never coarser, since a lower type at a node no other
// type reaches is not placed there and merges nothing (306 of 30,000 random cases finer, none
// coarser, none splitting two types whose meet is inhabited); the map of placements per cell
// and group, O(placements) memory. Why it is sound: merging nodes only joins more types, and a
// value two types share lies on one path from the root, whose every node both types reach,
// which reads it, so the keys that join them are read. Trigger: many cells that each reach
// one large group. Benchmarks: `types::empty::bench::types_that_each_reach_a_ring_of_names_scale`
// (the ring of names, the same under a one-tuple, and beside a whole under each name),
// `types_that_each_reach_a_ring_holding_lower_types_scale` (each member holding `#b_j((int,))`,
// `#b((int,))` under one name, or `#c_j((L,))` for a recursive list type `L`), each run on a
// copy of its own (`bench::rings_each`; FAIL-ratio-ring-shared-node: one copy shared by every
// run put a first run at 8k beside a later run at k, 10.50 or more), 8.10 to 8.16 times the
// instructions from k = 2,048 to 16,384; small instances of both in
// `types::empty::tests::the_rings_of_names_have_the_classes_their_shapes_give`; tests:
// `types_that_meet_are_joined_in_random_groups_holding_lower_types` (400 random cases against
// the meets), `types_that_each_reach_a_ring_of_names_are_apart`,
// `classes_inside_a_recursive_group_follow_its_merged_nodes`, and
// `l01_23_groups_and_refusals::group_oracle::verdicts_of_a_ring_of_the_group_that_hung_the_search_scale`.
// COMPLEXITY.md K36.
fn overlaps<'a>(ts: impl Iterator<Item = &'a Type>) -> Vec<Vec<usize>> {
    let none = Type::empty();
    let held = Held::default();
    let parts: Vec<&Parts> = ts.map(|t| t.p_held(&held)).collect();
    let n = parts.len();
    if n < 2 {
        return (0..n).map(|i| vec![i]).collect();
    }
    // Complexity tradeoff (`Π_sym`): partitioning `ts` by the join across universes of the meet
    // across components `0..m` and spine directions `dir in {0, 1}` makes `overlaps` reversal
    // invariant (`Z_2`) and strictly finer than base `overlaps` in `O(S log S)` time (with
    // two-slot `GROUPS` caching), whereas testing pairwise box meets exactly costs `O(n^2)`
    // emptiness searches (COMPLEXITY.md K36), and full `S_m` nested-spine invariance on arity
    // `m >= 3` would branch across all `m` components at each nested tuple depth (`O(m^d)`).
    // Each child at a tuple length: its index, whether it is whole, and its rows.
    type Kid<'r> = (usize, bool, Vec<&'r Row>);
    let mut by_m: BTreeMap<usize, Vec<Kid<'_>>> = BTreeMap::new();
    let mut base_tops: Vec<Top> = Vec::with_capacity(n);
    for (idx, p) in parts.iter().enumerate() {
        let l = local_dir(p, &none, 0);
        let mut kids = Vec::new();
        for kid in l.kids {
            match kid.edge {
                Edge::Len(1) => {
                    let mut top = (kid.edge, kid.bare, kid.whole, Vec::new());
                    match first_components(&p.tuples.lens[&1]) {
                        Some(q) => {
                            top.2 = false;
                            top.3.push(q);
                        }
                        None => top.3.extend(kid.inside.into_iter().cloned()),
                    }
                    kids.push(top);
                }
                Edge::Len(0) => {
                    kids.push((kid.edge, kid.bare, kid.whole, Vec::new()));
                }
                Edge::Len(m) => {
                    // A part that is `false` with no tuple type holding holds only tuples of
                    // the tuple types its paths to `true` take (`Part::taken_toward`), not
                    // those it refuses on every path, as `(1, 1)` in `(int, int) \ (1, 1)`.
                    // Each row once, in the order first met: how often the walk meets a row
                    // follows the draw of the treaps' priorities, the order of first meetings
                    // does not (`Type::function_part`; cross-review of PERF-xor-shape-free, Sol
                    // X2-F1).
                    let mut rows = Vec::new();
                    if !kid.whole {
                        let mut seen = DigestSet::default();
                        let mut met = BTreeSet::new();
                        let f = &p.tuples.lens[&m];
                        f.taken_toward(true, &mut seen, &mut |row| {
                            if met.insert(row) {
                                rows.push(row);
                            }
                        });
                    }
                    by_m.entry(m).or_default().push((idx, kid.whole, rows));
                }
                Edge::Atom(_) => {
                    kids.push((
                        kid.edge,
                        kid.bare,
                        kid.whole,
                        kid.inside.into_iter().cloned().collect(),
                    ));
                }
            }
        }
        base_tops.push(Top {
            points: l.points,
            lists: l.lists,
            kids,
        });
    }
    let mut p0 = joined(base_tops.clone(), 0);
    let mut parent: Vec<usize> = (0..n).collect();
    // When `p0` already separates all `n` inputs into singletons, `(r0_i, r1_i)` is distinct
    // for every `p1`, so `joined(base_tops, 1)` cannot refine further and is skipped.
    let p0_all_singletons = (0..n).all(|i| root(&mut p0, i) == i);
    if !p0_all_singletons {
        let mut p1 = joined(base_tops, 1);
        let mut base_first: HashMap<(usize, usize), usize> = HashMap::new();
        for i in 0..n {
            let key = (root(&mut p0, i), root(&mut p1, i));
            let j = *base_first.entry(key).or_insert(i);
            join(&mut parent, i, j);
        }
    }
    for (m, entries) in by_m {
        let k = entries.len();
        if k < 2 {
            continue;
        }
        let mut label_m: Vec<usize> = vec![0; k];
        let mut next_lbl = 1usize;
        let mut all_distinct = false;
        for c in 0..m {
            for dir in 0..2 {
                let tops: Vec<Top> = entries
                    .iter()
                    .map(|&(_i, whole, ref rows)| {
                        let inside = rows.iter().map(|r| r[c].clone()).collect();
                        Top {
                            points: Vec::new(),
                            lists: Vec::new(),
                            kids: vec![(Edge::Len(m), false, whole, inside)],
                        }
                    })
                    .collect();
                let mut p_run = joined(tops, dir);
                let mut fresh: HashMap<(usize, usize), usize> = HashMap::new();
                for (x, label) in label_m.iter_mut().enumerate().take(k) {
                    let r = root(&mut p_run, x);
                    *label = *fresh.entry((*label, r)).or_insert_with(|| {
                        let id = next_lbl;
                        next_lbl += 1;
                        id
                    });
                }
                if fresh.len() == k {
                    all_distinct = true;
                    break;
                }
            }
            if all_distinct {
                break;
            }
        }
        let mut m_first: HashMap<usize, usize> = HashMap::new();
        for (x, &(i, _, _)) in entries.iter().enumerate() {
            let j = *m_first.entry(label_m[x]).or_insert(i);
            join(&mut parent, i, j);
        }
    }
    let mut index: HashMap<usize, usize> = HashMap::new();
    let mut groups: Vec<Vec<usize>> = Vec::new();
    for i in 0..n {
        let r = root(&mut parent, i);
        let g = *index.entry(r).or_insert_with(|| {
            groups.push(Vec::new());
            groups.len() - 1
        });
        groups[g].push(i);
    }
    groups
}

/// What one type puts at the root of a run of [`overlaps`]: its keys and lists there, and per
/// edge below, whether it holds the bare atom of the name, whether it holds every value there,
/// and the types inside.
#[derive(Clone)]
struct Top {
    points: Vec<Key>,
    lists: Vec<Listed>,
    kids: Vec<(Edge, bool, bool, Vec<Type>)>,
}

/// A type that holds the first component of every one-tuple of the part `f` of one-tuples, when
/// one is read off `f` in time linear in it: when `f` is a meet of tuple types and complements
/// of tuple types (`Part::clause`), those of the meet of the tuple types it takes less those of
/// the ones it refuses ([`within_outside`]); otherwise those of the tuple types `T` that `f` takes
/// toward `true`, and those of what `f` holds with `T` false, when that is such a meet. A
/// one-tuple of `f` lies in a tuple type of `T`, or `f` holds it with every tuple type of `T`
/// false, which is the meet. `None` when the meet is no such part.
fn first_components(f: &Part<Row>) -> Option<Type> {
    if let Some((takes, refused)) = f.clause() {
        return Some(within_outside(&takes, &refused));
    }
    let mut seen = DigestSet::default();
    let mut taken: Vec<&Row> = Vec::new();
    f.taken_toward(true, &mut seen, &mut |r| taken.push(r));
    // The rows in their order, each once: how often the walk meets a row follows the draw of
    // the treaps' priorities (`Type::function_part`), and `union_all` pairs some components by
    // position (cross-review of PERF-xor-shape-free, Sol X2-F1).
    let set: BTreeSet<&Row> = taken.iter().copied().collect();
    let out = Type::union_all(set.iter().map(|r| r[0].clone()));
    let left = f.restrict(&|r| set.contains(r).then_some(false));
    if left.is_leaf() == Some(false) {
        return Some(out);
    }
    let (takes, refused) = left.clause()?;
    Some(&out | &within_outside(&takes, &refused))
}

/// A type that holds the first component of every one-tuple in the one-tuple types `takes` and
/// in none of `refused`: the meet of `takes`'s components, or every value, less those of
/// `refused`. A one-tuple is in a one-tuple type exactly when its component is in the type's.
fn within_outside(takes: &[Row], refused: &[Row]) -> Type {
    let within = Type::meet_all(takes.iter().map(|r| r[0].clone()));
    let outside = Type::union_all(refused.iter().map(|r| r[0].clone()));
    &within - &outside
}

/// One run of [`overlaps`]: the types of `tops` placed in one trie from its root; the
/// union-find of their indices, joined where two share a key.
fn joined(tops: Vec<Top>, dir: usize) -> Vec<usize> {
    let mut trie = Trie::new();
    let num_cells = tops.len();
    let mut s = Placing {
        active: vec![0; num_cells],
        pending_cnt: vec![0; num_cells],
        min_gid: vec![usize::MAX; num_cells],
        ..Placing::default()
    };
    s.sync(&trie);
    let mut parent: Vec<usize> = (0..num_cells).collect();
    // The groups placed for each cell, by cell and group number, with their placements. A
    // type of a group placed for the cell is placed: met again, its node and the new one are
    // merged.
    let mut placed: HashMap<(usize, usize), usize> = HashMap::new();
    // Complexity tradeoff: when `n` cells share a height-`n` chain of 1-member groups (such as
    // `G_i = #cons(int, G_i) | #cons(1, R_{i-1})` with `R_k = #cons(int, R_{k-1})` under `dir = 1`
    // in `by_place_from_the_end`, COMPLEXITY.md K35), placing `(i, g.id)` per cell and chain step
    // costs `Theta(n^2)` placements (`18.0x` at `64 -> 512`). Recording `(y_root, g.id) -> (j, y)`
    // once a deep `single_chain` root is read lets any later cell `i` with zero other active/pending
    // branches and `min_gid[i] > g.id` (Tarjan topological order, Tarjan 1972) join `j` in `O(1)`
    // with zero lost merges and an identical partition (`O(S log S)` in all), when `j` has no
    // node waiting (`pending_cnt[j] == 0`). Why: placing `g` for `i` at `y_root` walks the same
    // nodes as `j`'s placement, `g` merging no nodes and its lower groups placed for `i` for the
    // first time (`min_gid[i] > g.id`), so it adds no key and merges nothing that `join(i, j)`
    // does not give, except by reading a node of that walk that waits. A node waits for the
    // placement that made it, and every node of the walk is a node of `j`'s placements (a child
    // another cell made before `j` read its parent is read by `j`'s bind), so only `j`'s nodes can
    // wait there. Reading one makes `j` place its lower types there, which can merge two nodes
    // of `j` and join more types: FAIL-overlaps-order-ddc1ec274, where `#b(((0,),))` placed after
    // `#b(((0,),)) | (0,)` reads the node holding `0` under `#b` and merges it with the node of
    // `(0,)`, and the shortcut without this test skipped the read in one order and not the other
    // (test `overlaps_are_the_same_in_both_orders_when_a_chain_waits`). When `j` has a waiting
    // node, `i` is placed as before, which reads `j`'s waiting nodes on the walk, so a later cell
    // takes the shortcut: one extra walk per chain, the bound unchanged.
    let mut shared_chain: HashMap<(usize, usize), (usize, usize)> = HashMap::new();
    let mut work: Vec<Work> = Vec::new();
    for (i, l) in tops.into_iter().enumerate() {
        s.points.extend(l.points.into_iter().map(|k| (0, k, i)));
        s.lists.extend(l.lists.into_iter().map(|li| (0, li, i)));
        for (edge, bare, whole, inside) in l.kids {
            let y = trie.child(0, edge);
            s.sync(&trie);
            s.reach(&mut trie, y, &mut work);
            if bare {
                s.points.push((y, Key::Bare, i));
            }
            if whole {
                s.wholes.push((y, i));
            }
            s.active[i] += inside.len();
            work.extend(inside.into_iter().map(|t| Work::Place(y, t, i)));
        }
        while let Some(w) = work.pop() {
            match w {
                Work::Place(y, t, i) => {
                    s.active[i] -= 1;
                    let (g, c) = group_of(&t, dir);
                    let y_root = trie.find(y);
                    if c == 0 && s.active[i] == 0 && s.pending_cnt[i] == 0 && s.min_gid[i] > g.id {
                        if g.single_chain
                            && g.nodes[0].deep
                            && let Some(&(j, orig_y)) = shared_chain.get(&(y_root, g.id))
                            && trie.find(orig_y) == y_root
                            && s.pending_cnt[j] == 0
                        {
                            join(&mut parent, i, j);
                            continue;
                        }
                        if let Some(rs) = &g.repeat_stem
                            && rs.compressed
                            && s.pending[y_root].is_none()
                            && let Some(&y1_raw) = trie.kids[y_root].get(&rs.e0)
                        {
                            let y1 = trie.find(y1_raw);
                            let cycles = match &rs.second {
                                None => y1 == y_root,
                                Some((e1, _)) => {
                                    s.pending[y1].is_none()
                                        && trie.kids[y1]
                                            .get(e1)
                                            .copied()
                                            .is_some_and(|y2_raw| trie.find(y2_raw) == y_root)
                                }
                            };
                            if cycles {
                                s.min_gid[i] = g.id;
                                s.lists
                                    .extend(rs.l0.iter().cloned().map(|li| (y_root, li, i)));
                                if let Some((_, l1)) = &rs.second {
                                    s.lists.extend(l1.iter().cloned().map(|li| (y1, li, i)));
                                }
                                s.active[i] += 1;
                                work.push(Work::Place(y_root, rs.tail.clone(), i));
                                continue;
                            }
                        }
                    }
                    if g.id < s.min_gid[i] {
                        s.min_gid[i] = g.id;
                    }
                    let p = *placed.entry((i, g.id)).or_insert_with(|| {
                        s.groups.push(g);
                        s.cells.push(i);
                        s.at.push(HashMap::new());
                        s.at.len() - 1
                    });
                    match s.at[p].get(&c) {
                        Some(&z) => work.push(Work::Merge(z, y)),
                        None => {
                            s.at[p].insert(c, y);
                            s.active[i] += 1;
                            work.push(Work::Bind(y, p, c));
                        }
                    }
                }
                Work::Bind(y, p, q) => {
                    let cell_i = s.cells[p];
                    s.active[cell_i] -= 1;
                    let y = trie.find(y);
                    s.reach(&mut trie, y, &mut work);
                    let y = trie.find(y);
                    if q == 0 && s.groups[p].single_chain && s.groups[p].nodes[0].deep {
                        shared_chain
                            .entry((y, s.groups[p].id))
                            .or_insert((cell_i, y));
                    }
                    s.read(&mut trie, y, p, q, &mut work);
                }
                Work::Merge(a, b) => {
                    trie.merge_with(a, b, |trie, x| s.reach(trie, x, &mut work));
                }
            }
        }
    }
    let Placing {
        groups: placed_groups,
        cells,
        at: placements,
        pending,
        mut points,
        lists,
        wholes,
        ..
    } = s;
    // Each node's merged node, from here on its name.
    let at: Vec<usize> = (0..trie.same.len()).map(|x| trie.find(x)).collect();
    // Per node and universe with a cofinite type, the keys every cofinite type there lists.
    let mut cofinites: BTreeMap<(usize, usize), Vec<usize>> = BTreeMap::new();
    for (l, (x, (u, cofinite, _), _)) in lists.iter().enumerate() {
        if *cofinite {
            cofinites.entry((at[*x], *u)).or_default().push(l);
        }
    }
    let shut: BTreeMap<(usize, usize), BTreeSet<&Key>> = cofinites
        .into_iter()
        .map(|(at, ls)| {
            let shortest = *ls
                .iter()
                .min_by_key(|&&l| lists[l].1.2.len())
                .expect("a group has a list");
            let mut meet: BTreeSet<&Key> = lists[shortest].1.2.iter().map(|(k, _)| k).collect();
            for &l in &ls {
                if l != shortest {
                    let ks: BTreeSet<&Key> = lists[l].1.2.iter().map(|(k, _)| k).collect();
                    meet.retain(|k| ks.contains(k));
                }
            }
            (at, meet)
        })
        .collect();
    for (x, (u, cofinite, ks), i) in &lists {
        let outside = |s: &BTreeSet<&Key>| ks.iter().any(|(k, held)| *held && !s.contains(k));
        if *cofinite || shut.get(&(at[*x], *u)).is_some_and(outside) {
            points.push((*x, Key::All(*u), *i));
        }
    }
    // Per node, a type that holds every value under it or under a node above it. Merged nodes
    // can make a node the child of several nodes, or of one below it, so each node gets a type
    // once and passes it to its children once. Below a node not read is only its placement's
    // cell, which a type holding every value above the node shares a value with when the
    // group node is deep ([`Group::set_deep`]). Below a node not read with children is also
    // every node of its group, since each node with children holds a member of the group,
    // which reaches every member: such a type enters the placement, passing to the nodes of
    // the placement read, once per placement.
    let mut whole: Vec<Option<usize>> = vec![None; at.len()];
    let mut entered: Vec<Option<usize>> = vec![None; placed_groups.len()];
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
    // The placements entered, with the type that enters.
    let mut enter: Vec<(usize, usize)> = Vec::new();
    loop {
        if let Some((p, w)) = enter.pop() {
            if let Some(v) = entered[p] {
                join(&mut parent, v, w);
                continue;
            }
            entered[p] = Some(w);
            for &y in placements[p].values() {
                let y = at[y];
                if pending[y].is_some() {
                    continue;
                }
                match whole[y] {
                    Some(v) => join(&mut parent, v, w),
                    None => {
                        whole[y] = Some(w);
                        down.push(y);
                    }
                }
            }
            continue;
        }
        let Some(x) = down.pop() else { break };
        let w = whole[x].expect("a node passed down has a type");
        for &c in trie.kids[x].values() {
            let c = at[c];
            let Some((p, q)) = pending[c] else {
                match whole[c] {
                    Some(v) => join(&mut parent, v, w),
                    None => {
                        whole[c] = Some(w);
                        down.push(c);
                    }
                }
                continue;
            };
            let n = &placed_groups[p].nodes[q];
            if n.deep {
                join(&mut parent, w, cells[p]);
            }
            if !n.kids.is_empty() {
                enter.push((p, w));
            }
        }
    }
    let mut first: BTreeMap<(usize, Key), usize> = BTreeMap::new();
    for (x, k, i) in points {
        let x = at[x];
        let j = *first.entry((x, k)).or_insert(i);
        join(&mut parent, i, j);
        if let Some(w) = whole[x] {
            join(&mut parent, i, w);
        }
    }
    parent
}

/// Whether `k` is known empty for good without a search: the empty type, or a recursive type
/// its group decided empty. A type the search reads is not taken, since its answer may rest on
/// an assumption the search later drops.
fn known_empty(k: &Type) -> bool {
    *k == Type::empty() || k.judged() == Some(true)
}

/// Each member's emptiness at `env`'s arguments, as the group's fixed points decide it (module
/// `bes`, cross-review X14): a union is an `Or` node, a tuple or atom payload an `And` node, a
/// morphism type whose guarantee lies within its permission and is inhabited a `Mor` node of
/// its value type, and a part that does not mention the group `Top` or `Bot` by its own
/// emptiness. A cycle through a tuple is then empty and one through a morphism's value type
/// inhabited.
///
/// A meet `a & b` or a difference `a \ b` with a recursive occurrence in it (admission keeps
/// such an occurrence out of a complement and the right of `\`) is read by what it lies
/// within (plan item GROUP-setop): the meet as an `And` node of its operands, which is
/// inhabited when each operand is, and the difference as its left operand. Each holds at least
/// the values of the type it stands for, so a member decided empty is empty. A member decided
/// inhabited is so only if its node reaches none of these: `#b \ #b` is empty and `#b` is not,
/// and `#a & #b` is empty while both are inhabited. Those members are `None` here and go to
/// the search ([`group_verdicts`]).
///
/// A part the decider does not take (a morphism with recursive bounds it does not admit, a
/// closed part whose verdict is refused) is a leaf with no children, and the system is decided
/// twice, the leaves `Bot` and then `Top` (item GROUP-refusal). Every node's answer is monotone
/// in each leaf, and the leaves' true values lie between the two, so a member inhabited with
/// the leaves `Bot`, or empty with them `Top`, is so; a member the two runs decide differently
/// rests on a leaf and goes to the search, with the members decided here read by their
/// answers. A member the decider refuses in either run goes to the search too, and if the
/// search does not decide it, its verdict is refused with its own message
/// ([`Type::refusal_site`]).
///
/// A member the system leaves open is read in other systems of the same types ([`Others`]): the
/// system with the arms dropped that a union also reaches through another union it names
/// ([`names::absorb`], item GROUP-cycle-dup-names), the system with the nodes that play alike
/// merged, among them equal parts of two definitions ([`names::merged`], item
/// GROUP-cycle-dup-across), and that with those arms dropped; the system with arms dropped is
/// merged too, after each union left with one arm is read as that arm ([`names::contracted`],
/// item GROUP-arm-drop-merge), so parts equal once arms are dropped are one node. A member any of them decides is
/// decided, since each answer is the type's. The refusal message reads the system as written,
/// whose nodes keep the definition that wrote them. Time linear in the bodies, besides the
/// emptiness of their closed parts, the O(m log m) of [`names::absorb`] and the O(m log n) of
/// [`names::merged`].
fn judge(env: &Arc<Env>) -> Judgment {
    let bodies = &env.group().0.bodies;
    let System {
        mut b,
        origin,
        meets,
        mut wider,
        leaves,
        same,
        union,
    } = system(env);
    // The nodes that reach a meet or a difference, by their parents, each node once.
    let mut wide = vec![false; b.len()];
    for &v in &wider {
        wide[v as usize] = true;
    }
    while let Some(v) = wider.pop() {
        for &p in b.parents(v) {
            if !wide[p as usize] {
                wide[p as usize] = true;
                wider.push(p);
            }
        }
    }
    let mut runs = vec![decide(&b)];
    if !leaves.is_empty() {
        // A leaf has no children either way, so the parents `seal` filled stay right.
        for &v in &leaves {
            b.set(v, Kind::Top, vec![]);
        }
        runs.push(decide(&b));
    }
    // Complexity tradeoff: a member shown inhabited through a meet or a difference goes to the
    // search, which builds a value of the meet: one state of the product of its operands per
    // node it reads. Why: the decider's answer is not exact there (`#a & #b`). Trigger: an
    // `Inhabited` answer on a node that reaches a meet or a difference. Cost: linear in the
    // meet's operands when a short value exists (`l01_23_subtyping::setop::meets_of_k_members_scale`,
    // 7.1 times at k 8 and 64); exponential when the search forks on the product, which the
    // verdict refuses as `Refusal::Fork` after a search for a value. The parity
    // product instead uses its checked singleton
    // (`parity_verdicts_scale_with_the_number_of_constraints`). COMPLEXITY.md K84. Naive version: a recursive occurrence
    // under `&` or `\` makes the decider give up the whole group, so every member goes to the
    // search (3.15M and 73.2M instructions at k 8 and 64, 23 times). Used: the decider reads
    // `a & b` as an `And` node of its operands and `a \ b` as `a`, linear in the group, its
    // `Empty` answers exact, so only members shown inhabited through a meet or a difference
    // are searched (603K and 4.34M at k 8 and 64). A complete solution needs the product
    // construction of the meet's tree automata, exponential in the number of operands
    // (emptiness of an intersection of tree automata is EXPTIME-complete).
    let n = bodies.len();
    let (low, high) = (&runs[0], &runs[runs.len() - 1]);
    let named: Vec<Option<bool>> = (0..n)
        .map(|i| settled(low.answers[i], high.answers[i], wide[i]))
        .collect();
    // The other systems are read only for a member `b` leaves open. With debug assertions they
    // are decided for every group, for the assertion that they agree.
    let others = (cfg!(debug_assertions) || named.contains(&None))
        .then(|| Others::new(&mut b, &leaves, &same, &union));
    let (mut answers, mut refused) = (vec![None; n], vec![false; n]);
    for i in 0..n {
        let mut read = others.iter().flat_map(|o| o.answers(i, wide[i]));
        let first = named[i].or_else(|| read.next());
        debug_assert!(
            read.all(|r| Some(r) == first),
            "the systems of one group's types agree"
        );
        answers[i] = first;
        refused[i] = first.is_none()
            && (low.answers[i] == Answer::Refused || high.answers[i] == Answer::Refused);
    }
    if wide.contains(&true) && answers.contains(&None) {
        exact_flat_diff_decide(env, &mut answers, &mut refused);
    }
    let why = refused
        .contains(&true)
        .then(|| Why::new(n, b, origin, meets, runs, wide));
    Judgment {
        answers,
        refused,
        why,
    }
}

/// Whether `t` holds only flat values (scalars, bare atoms, 0-tuples, structs).
fn is_flat_type(t: &Type) -> bool {
    let p = t.p();
    !p.atoms.cofinite()
        && p.atoms.payloads().is_empty()
        && !p.tuples.rest
        && p.tuples
            .lens
            .iter()
            .all(|(&len, f)| len == 0 || f.is_leaf() == Some(false))
        && p.morphisms.is_leaf() == Some(false)
}

/// The exact flat projection `[[t]] \cap Val_flat`, when `!t.p().atoms.cofinite`.
fn flat_part(t: &Type) -> Option<Type> {
    let p = t.p();
    if p.atoms.cofinite() {
        return None;
    }
    Some(Type::with(|q| {
        q.bools = p.bools;
        q.ints = p.ints.clone();
        q.rats = p.rats.clone();
        q.floats = p.floats.clone();
        q.f32s = p.f32s.clone();
        q.strings = p.strings.clone();
        q.structs = p.structs;
        let f0 = p.tuples.get(0);
        if f0.is_leaf() != Some(false) {
            q.tuples.lens.insert(0, f0);
        }
        q.atoms = p.atoms.clone();
        for name in p.atoms.payloads().iter() {
            let bare = p.atoms.get(name).bare;
            q.atoms.set(
                name,
                super::AtomPart {
                    bare,
                    payload: Type::empty(),
                },
            );
        }
    }))
}

/// A non-flat projection inside `[[t]] \cap Val_nonflat` that is exact on emptiness (equal to
/// `[[t]] \cap Val_nonflat` when `!p.atoms.cofinite`, and containing a witness payload atom
/// `#nf_k(())` when `p.atoms.cofinite`, with zero bare atoms or 0-tuples in all cases).
fn nonflat_part(t: &Type) -> Type {
    let p = t.p();
    Type::with(|q| {
        q.tuples = p.tuples.clone();
        if q.tuples.rest {
            q.tuples.lens.insert(0, Part::leaf(false));
        } else {
            q.tuples.lens.remove(&0);
        }
        q.morphisms = p.morphisms.clone();
        if p.atoms.cofinite() {
            for (name, a) in p.atoms.names().iter() {
                if a.payload != Type::empty() {
                    q.atoms.set(
                        name,
                        super::AtomPart {
                            bare: false,
                            payload: a.payload.clone(),
                        },
                    );
                }
            }
            let mut k = 0usize;
            let fresh: std::sync::Arc<str> = loop {
                let cand: std::sync::Arc<str> = format!("nf_{k}").into();
                if !p.atoms.names().contains_key(&cand) {
                    break cand;
                }
                k += 1;
            };
            q.atoms.set(
                &fresh,
                super::AtomPart {
                    bare: false,
                    payload: Type::payloads(),
                },
            );
        } else {
            q.atoms = p.atoms.clone();
            // Only the bare names (`Atoms::bare`), O(b log n) for their b, not every name.
            for name in p.atoms.bare() {
                let a = p.atoms.get(name);
                q.atoms.set(
                    name,
                    super::AtomPart {
                        bare: false,
                        payload: a.payload,
                    },
                );
            }
        }
    })
}

/// Depth-0 check whether the top-level universes of `ts` have empty intersection.
fn disjoint_top_carriers_depth0(ts: &[Type]) -> bool {
    if ts.len() < 2 {
        return false;
    }
    let flat_meet_nonempty = {
        let mut iter = ts.iter();
        if let Some(first) = iter.next().and_then(flat_part) {
            let mut acc = Some(first);
            for t in iter {
                match (acc, flat_part(t)) {
                    (Some(a), Some(b)) => acc = Some(&a & &b),
                    _ => {
                        acc = None;
                        break;
                    }
                }
            }
            match acc {
                Some(m) => !m.is_empty(),
                None => true,
            }
        } else {
            ts.iter().all(|t| {
                let p = t.p();
                p.atoms.cofinite() || p.has_scalars() || p.has_bare_atoms() || p.structs
            })
        }
    };
    if flat_meet_nonempty {
        return false;
    }
    if ts.iter().all(|t| t.p().morphisms.is_leaf() != Some(false)) {
        return false;
    }
    let share_payload_atom = {
        let p0 = ts[0].p();
        if p0.atoms.cofinite() {
            ts[1..]
                .iter()
                .all(|t| t.p().atoms.cofinite() || !t.p().atoms.payloads().is_empty())
        } else {
            p0.atoms.payloads().iter().any(|name| {
                ts[1..].iter().all(|t| {
                    let pt = t.p();
                    if pt.atoms.cofinite() {
                        pt.atoms
                            .names()
                            .get(name)
                            .is_none_or(|a| a.payload != Type::empty())
                    } else {
                        pt.atoms.payloads().contains(name)
                    }
                })
            })
        }
    };
    if share_payload_atom {
        return false;
    }
    let all_rest = ts.iter().all(|t| t.p().tuples.rest);
    if all_rest {
        return false;
    }
    if let Some(anchor) = ts.iter().find(|t| !t.p().tuples.rest) {
        let pa = anchor.p();
        let share_len = pa.tuples.lens.iter().any(|(&len, fa)| {
            len >= 1
                && fa.is_leaf() != Some(false)
                && ts.iter().all(|t| {
                    let pt = t.p();
                    if pt.tuples.rest {
                        pt.tuples
                            .lens
                            .get(&len)
                            .is_none_or(|ft| ft.is_leaf() != Some(false))
                    } else {
                        pt.tuples
                            .lens
                            .get(&len)
                            .is_some_and(|ft| ft.is_leaf() != Some(false))
                    }
                })
        });
        if share_len {
            return false;
        }
    }
    true
}

/// The universes a type's parts may hold, one bit each: booleans, the five literal carriers,
/// atoms, tuples, structs and morphisms, the split of [`Parts::scalars_only`]. A bit may be
/// set for an empty part; a value of the type always has its universe's bit set.
fn universe_mask(t: &Type) -> u16 {
    let p = t.p();
    let lits = |l: &Lits| l.cofinite || !l.values.is_empty();
    [
        p.bools != 0,
        lits(&p.ints),
        lits(&p.rats),
        lits(&p.floats),
        lits(&p.strings),
        lits(&p.f32s),
        !p.atoms.is_default(),
        !p.tuples.is_default(),
        p.structs,
        p.morphisms.is_leaf() != Some(false),
    ]
    .iter()
    .enumerate()
    .fold(0, |m, (i, &b)| m | (u16::from(b) << i))
}

/// The union of [`universe_mask`] of the cells at component `j` over the rows of the tuple part
/// `f`, with whether a cell is a recursive type by name: every value of `f` has its component
/// `j` in a universe of it when `f` is false with every row false (each value then lies in one
/// row it holds), else `None`. A recursive cell is unfolded one step only when `unfold`, else
/// it counts as every universe.
fn component_carrier(f: &Part<Row>, j: usize, unfold: bool) -> Option<(u16, bool)> {
    if f.eval3(&|_| Some(false)) != Some(false) {
        return None;
    }
    let (mut u, mut rec) = (0, false);
    f.atoms(&mut |row| {
        let c = &row[j];
        rec |= c.is_recursive();
        u |= if c.is_recursive() && !unfold {
            u16::MAX
        } else {
            universe_mask(c)
        };
        true
    });
    Some((u, rec))
}

/// Whether `ts` have provably empty intersection by their top-level universes, or, when only
/// tuples of shared lengths `m >= 1` meet there, because at one component of each such length
/// the universe masks ([`component_carrier`]) of the types have no bit in common; no cycle is
/// followed (deciding seed 1865 the same in both component orders).
// Complexity tradeoff (GROUP-order-cpoly-merge): the depth-0 test reads the top parts of `ts`;
// the component test reads, for each shared length `m`, each cell of each type's rows at most
// twice per component, `O(\sum_m m R_m)` part reads and bit operations for `R_m` rows, with no
// type built, and a recursive cell is unfolded one step only on the second read. Round 3 of
// XR-group-order-5 (Gemini) built conjunctive projection types per component instead, capped
// at 4 conjuncts per node (a size switch the no-thresholds rule forbids) and building a union
// type per row; that version separated values within one universe (`1` from `2`), which the
// masks do not, and no test of the l01_23 groups needs it (measured: the full l01_23 and
// zed-kernel suites pass with the masks). Exact emptiness of a meet of cyclic types is
// tree-automata intersection, EXPTIME-complete in the number of conjuncts (Seidl 1994), left to
// the search; directional single-spine `overlaps` merged `M0` with `int` when reversed on seed
// 1865.
fn disjoint_top_carriers(ts: &[Type]) -> bool {
    if ts.len() < 2 {
        return false;
    }
    if disjoint_top_carriers_depth0(ts) {
        return true;
    }
    // Check whether non-tuple universes already overlap; if so, depth-1 tuple projections alone
    // cannot prove `ts` disjoint.
    let no_tuple_ts: Vec<Type> = ts
        .iter()
        .map(|t| {
            let p = t.p();
            Type::with(|q| {
                q.bools = p.bools;
                q.ints = p.ints.clone();
                q.rats = p.rats.clone();
                q.floats = p.floats.clone();
                q.f32s = p.f32s.clone();
                q.strings = p.strings.clone();
                q.structs = p.structs;
                let f0 = p.tuples.get(0);
                if f0.is_leaf() != Some(false) {
                    q.tuples.lens.insert(0, f0);
                }
                q.atoms = p.atoms.clone();
                q.morphisms = p.morphisms.clone();
            })
        })
        .collect();
    if !disjoint_top_carriers_depth0(&no_tuple_ts) {
        return false;
    }
    if ts.iter().any(|t| t.p().tuples.rest) {
        return false;
    }
    let p0 = ts[0].p();
    let shared_lens: Vec<usize> = p0
        .tuples
        .lens
        .iter()
        .filter_map(|(&m, f0)| {
            (m >= 1
                && f0.is_leaf() != Some(false)
                && ts[1..].iter().all(|t| {
                    t.p()
                        .tuples
                        .lens
                        .get(&m)
                        .is_some_and(|ft| ft.is_leaf() != Some(false))
                }))
            .then_some(m)
        })
        .collect();
    for m in shared_lens {
        let separated = (0..m).any(|c| {
            // The meet of the masks at `c`, and whether some type has no recursive cell there.
            let meet = |unfold| {
                ts.iter().try_fold((u16::MAX, false), |(acc, plain), t| {
                    let p = t.p();
                    let ft = p.tuples.lens.get(&m)?;
                    component_carrier(ft, c, unfold).map(|(u, rec)| (acc & u, plain || !rec))
                })
            };
            // Recursive cells are unfolded one step only when another type's cells at `c` are
            // all read without unfolding.
            match meet(false) {
                Some((0, _)) => true,
                Some((_, true)) => meet(true).is_some_and(|(u, _)| u == 0),
                _ => false,
            }
        });
        if !separated {
            return false;
        }
    }
    true
}

/// If `r_ty`'s `m`-tuple part (restricted to rows whose components can overlap `xs_tys`) is false
/// outside its rows and every cell of those surviving rows is flat, returns that isolated `m`-tuple
/// `Type`.
fn flat_tuple_subtrahend(r_ty: &Type, xs_tys: &[Type]) -> Option<Type> {
    let m = xs_tys.len();
    let p = r_ty.p();
    if p.tuples.rest {
        return None;
    }
    let Some(f) = p.tuples.lens.get(&m) else {
        return Some(Type::empty());
    };
    if f.is_leaf() == Some(false) {
        return Some(Type::empty());
    }
    let f_rel = f.restrict(&|row| {
        let disj = (0..m).any(|j| disjoint_top_carriers(&[xs_tys[j].clone(), row[j].clone()]));
        disj.then_some(false)
    });
    if f_rel.is_leaf() == Some(false) {
        return Some(Type::empty());
    }
    if f_rel.eval3(&|_| Some(false)) != Some(false) {
        return None;
    }
    let mut all_flat = true;
    f_rel.atoms(&mut |row| {
        if row.iter().any(|cell| !is_flat_type(cell)) {
            all_flat = false;
            return false;
        }
        true
    });
    if !all_flat {
        return None;
    }
    Some(Type::with(|q| {
        q.tuples.lens.insert(m, f_rel);
    }))
}

/// Exact 2-layer BES (`Inh` and `NonFlat`) decision for groups in `C_group` (no overlapping
/// multi-recursive `And`, and `Diff` subtrahends either empty or flat / flat-tuple).
// Complexity tradeoff: decides emptiness of recursive groups in `C_group` in `O(S)` BES size
// (plus finite flat-box sub-checks on non-recursive subtrahends) by tracking `Inh(X)` (`[[X]] !=
// \emptyset`) and `NonFlat(X)` (`[[X]] \cap Val_nonflat != \emptyset`) in a monotone two-layer
// Boolean equation system solved in linear time (`bes::decide`, following Dowling & Gallier 1984
// linear-time Horn / least-fixed-point reachability and Lu & Cleary 1998 regular type emptiness),
// whereas general intersection/complementation of recursive tree automata is EXPTIME-complete.
fn exact_flat_diff_decide(
    env: &Arc<Env>,
    answers: &mut [Option<bool>],
    refused: &mut [bool],
) -> Option<()> {
    enum Step<'a> {
        Visit(&'a Arc<rec::Node>),
        Make(&'a Arc<rec::Node>, usize),
    }
    let bodies = &env.group().0.bodies;
    let n = bodies.len();
    let mut b = Bes::new();
    // Nodes `0..n` are `Inh(member i)`; nodes `n..2*n` are `NonFlat(member i)`.
    for _ in 0..(2 * n) {
        b.add(Kind::Bot, vec![]);
    }
    let top_node = b.add(Kind::Top, vec![]);
    let bot_node = b.add(Kind::Bot, vec![]);

    let mut eval_cache: HashMap<u32, Type> = HashMap::new();
    let mut eval_cached = |node: &Arc<rec::Node>| -> Type {
        eval_cache
            .entry(node.class)
            .or_insert_with(|| eval(node, env))
            .clone()
    };

    let mut seen: HashMap<u32, (u32, u32)> = HashMap::new();
    let mut todo: Vec<Step<'_>> = Vec::new();
    let mut done: Vec<(u32, u32)> = Vec::new();

    for (def, body) in bodies.iter().enumerate() {
        todo.push(Step::Visit(body));
        while let Some(step) = todo.pop() {
            match step {
                Step::Visit(e) => {
                    let root = Arc::ptr_eq(e, body);
                    if let rec::Shape::Ref(i, _) = e.e {
                        let pair = (i as u32, (n + i) as u32);
                        if root {
                            b.set(def as u32, Kind::Or, vec![pair.0]);
                            b.set((n + def) as u32, Kind::Or, vec![pair.1]);
                        } else {
                            done.push(pair);
                        }
                        continue;
                    }
                    if let Some(&pair) = seen.get(&e.class) {
                        if root {
                            b.set(def as u32, Kind::Or, vec![pair.0]);
                            b.set((n + def) as u32, Kind::Or, vec![pair.1]);
                        } else {
                            done.push(pair);
                        }
                        continue;
                    }
                    if !e.recursive {
                        let t = eval_cached(e);
                        // `a \ r` lies in `a`, and a meet in each operand: an operand already
                        // proved empty makes the node empty without searching the whole (Seed 1558).
                        let operand_empty = match &e.e {
                            rec::Shape::Diff(a, _) => eval_cached(a).verdict() == Verdict::Empty,
                            rec::Shape::And(xs) => xs
                                .iter()
                                .any(|x| eval_cached(x).verdict() == Verdict::Empty),
                            _ => false,
                        };
                        let v = if operand_empty {
                            Verdict::Empty
                        } else {
                            t.verdict()
                        };
                        let pair = match v {
                            Verdict::Empty => (bot_node, bot_node),
                            Verdict::Refused(_) => return None,
                            Verdict::Inhabited => {
                                let nf_t = nonflat_part(&t);
                                let nf = match nf_t.verdict() {
                                    Verdict::Empty => bot_node,
                                    Verdict::Inhabited => top_node,
                                    Verdict::Refused(_) => return None,
                                };
                                (top_node, nf)
                            }
                        };
                        seen.insert(e.class, pair);
                        if root {
                            b.set(def as u32, Kind::Or, vec![pair.0]);
                            b.set((n + def) as u32, Kind::Or, vec![pair.1]);
                        } else {
                            done.push(pair);
                        }
                        continue;
                    }
                    match &e.e {
                        rec::Shape::Morphism(l, u, val) if l.recursive || u.recursive => {
                            if !val.recursive && eval_cached(val).verdict() == Verdict::Inhabited {
                                let pair = (top_node, top_node);
                                seen.insert(e.class, pair);
                                if root {
                                    b.set(def as u32, Kind::Top, vec![]);
                                    b.set((n + def) as u32, Kind::Top, vec![]);
                                } else {
                                    done.push(pair);
                                }
                            } else {
                                return None;
                            }
                        }
                        rec::Shape::Morphism(l, u, val) => {
                            let (lt, ut) = (eval_cached(l), eval_cached(u));
                            match (lt.subtype_verdict(&ut), lt.verdict()) {
                                (Verdict::Refused(_), _) | (_, Verdict::Refused(_)) => return None,
                                (Verdict::Inhabited, _) => {
                                    let pair = (bot_node, bot_node);
                                    seen.insert(e.class, pair);
                                    if root {
                                        b.set(def as u32, Kind::Bot, vec![]);
                                        b.set((n + def) as u32, Kind::Bot, vec![]);
                                    } else {
                                        done.push(pair);
                                    }
                                }
                                (Verdict::Empty, Verdict::Empty) => {
                                    let pair = (top_node, top_node);
                                    seen.insert(e.class, pair);
                                    if root {
                                        b.set(def as u32, Kind::Top, vec![]);
                                        b.set((n + def) as u32, Kind::Top, vec![]);
                                    } else {
                                        done.push(pair);
                                    }
                                }
                                (Verdict::Empty, Verdict::Inhabited) => {
                                    todo.push(Step::Make(e, 1));
                                    todo.push(Step::Visit(val));
                                }
                            }
                        }
                        rec::Shape::Union(xs) | rec::Shape::Tuple(xs) | rec::Shape::Atom(_, xs) => {
                            todo.push(Step::Make(e, xs.len()));
                            todo.extend(xs.iter().rev().map(Step::Visit));
                        }
                        rec::Shape::And(xs) => {
                            let tys: Vec<Type> = xs.iter().map(&mut eval_cached).collect();
                            if disjoint_top_carriers(&tys) {
                                let pair = (bot_node, bot_node);
                                seen.insert(e.class, pair);
                                if root {
                                    b.set(def as u32, Kind::Bot, vec![]);
                                    b.set((n + def) as u32, Kind::Bot, vec![]);
                                } else {
                                    done.push(pair);
                                }
                                continue;
                            }
                            let mut rec_keys = BTreeSet::new();
                            for x in xs {
                                if x.recursive {
                                    let key = match &x.e {
                                        rec::Shape::Ref(i, a) if a.is_empty() => (0u8, *i as u32),
                                        _ => (1u8, x.class),
                                    };
                                    rec_keys.insert(key);
                                }
                            }
                            if rec_keys.len() >= 2 {
                                return None;
                            }
                            todo.push(Step::Make(e, xs.len()));
                            todo.extend(xs.iter().rev().map(Step::Visit));
                        }
                        rec::Shape::Diff(a, _) => {
                            todo.push(Step::Make(e, 1));
                            todo.push(Step::Visit(a));
                        }
                        rec::Shape::Not(_)
                        | rec::Shape::Param(_)
                        | rec::Shape::Type(_)
                        | rec::Shape::Ref(..) => return None,
                    }
                }
                Step::Make(e, k) => {
                    let root = Arc::ptr_eq(e, body);
                    let parts = done.split_off(done.len() - k);
                    let pair = match &e.e {
                        rec::Shape::Union(_) => {
                            let mut inhs: Vec<u32> = parts.iter().map(|p| p.0).collect();
                            let mut nfs: Vec<u32> = parts.iter().map(|p| p.1).collect();
                            inhs.sort_unstable();
                            inhs.dedup();
                            nfs.sort_unstable();
                            nfs.dedup();
                            (b.add(Kind::Or, inhs), b.add(Kind::Or, nfs))
                        }
                        rec::Shape::Tuple(xs) => {
                            if xs.is_empty() {
                                (top_node, bot_node)
                            } else {
                                let inhs: Vec<u32> = parts.iter().map(|p| p.0).collect();
                                let u = b.add(Kind::And, inhs);
                                (u, u)
                            }
                        }
                        rec::Shape::Atom(_, xs) => {
                            if xs.is_empty() {
                                (top_node, bot_node)
                            } else {
                                let inhs: Vec<u32> = parts.iter().map(|p| p.0).collect();
                                let u = b.add(Kind::And, inhs);
                                (u, u)
                            }
                        }
                        rec::Shape::Morphism(..) => {
                            let u = b.add(Kind::Mor, vec![parts[0].0]);
                            (u, u)
                        }
                        rec::Shape::And(xs) => {
                            // At most 1 distinct recursive operand, and carriers overlap.
                            let mut closed_meet = Type::top();
                            let mut rec_idx = None;
                            for (idx, x) in xs.iter().enumerate() {
                                if x.recursive {
                                    rec_idx = Some(idx);
                                } else {
                                    closed_meet = &closed_meet & &eval_cached(x);
                                }
                            }
                            let idx = rec_idx?;
                            if closed_meet.verdict() == Verdict::Empty {
                                (bot_node, bot_node)
                            } else if closed_meet == Type::top() {
                                parts[idx]
                            } else if is_flat_type(&closed_meet) {
                                let x_flat = flat_part(&eval_cached(&xs[idx]))?;
                                let m = &x_flat & &closed_meet;
                                let inh = if m.is_empty() { bot_node } else { top_node };
                                (inh, bot_node)
                            } else {
                                return None;
                            }
                        }
                        rec::Shape::Diff(a, r) => {
                            let r_ty = eval_cached(r);
                            let r_empty = match &r.e {
                                rec::Shape::Diff(ra, _) if !r.recursive => {
                                    eval_cached(ra).verdict() == Verdict::Empty
                                }
                                rec::Shape::And(rxs) if !r.recursive => rxs
                                    .iter()
                                    .any(|x| eval_cached(x).verdict() == Verdict::Empty),
                                _ => false,
                            };
                            let r_verdict = if r_empty {
                                Verdict::Empty
                            } else {
                                r_ty.verdict()
                            };
                            match r_verdict {
                                Verdict::Empty => parts[0],
                                Verdict::Refused(_) => return None,
                                Verdict::Inhabited if is_flat_type(&r_ty) => {
                                    let a_flat = flat_part(&eval_cached(a))?;
                                    let rem = &a_flat - &r_ty;
                                    let inh = if !rem.is_empty() {
                                        top_node
                                    } else {
                                        parts[0].1
                                    };
                                    (inh, parts[0].1)
                                }
                                Verdict::Inhabited => {
                                    let rec::Shape::Tuple(xs) = &a.e else {
                                        return None;
                                    };
                                    let m = xs.len();
                                    if m == 0 {
                                        return None;
                                    }
                                    let xs_tys: Vec<Type> =
                                        xs.iter().map(&mut eval_cached).collect();
                                    let r_ty_m = flat_tuple_subtrahend(&r_ty, &xs_tys)?;
                                    let mut flats = Vec::with_capacity(m);
                                    let mut xs_inh = Vec::with_capacity(m);
                                    let mut xs_nf = Vec::with_capacity(m);
                                    for (j, x) in xs.iter().enumerate() {
                                        flats.push(flat_part(&xs_tys[j])?);
                                        let pair = match &x.e {
                                            rec::Shape::Ref(i, _) => (*i as u32, (n + *i) as u32),
                                            _ => *seen.get(&x.class)?,
                                        };
                                        xs_inh.push(pair.0);
                                        xs_nf.push(pair.1);
                                    }
                                    let flat_diff = &Type::tuple(flats) - &r_ty_m;
                                    match flat_diff.verdict() {
                                        Verdict::Refused(_) => return None,
                                        Verdict::Inhabited => {
                                            let u = b.add(Kind::And, xs_inh);
                                            (u, u)
                                        }
                                        Verdict::Empty => {
                                            let any_nf = b.add(Kind::Or, xs_nf);
                                            xs_inh.push(any_nf);
                                            let u = b.add(Kind::And, xs_inh);
                                            (u, u)
                                        }
                                    }
                                }
                            }
                        }
                        _ => return None,
                    };
                    seen.insert(e.class, pair);
                    if root {
                        b.set(def as u32, Kind::Or, vec![pair.0]);
                        b.set((n + def) as u32, Kind::Or, vec![pair.1]);
                    } else {
                        done.push(pair);
                    }
                }
            }
        }
    }

    b.seal();
    let dec = decide(&b);
    for i in 0..n {
        if answers[i].is_none() {
            match dec.answers[i] {
                Answer::Empty => {
                    answers[i] = Some(true);
                    refused[i] = false;
                }
                Answer::Inhabited => {
                    answers[i] = Some(false);
                    refused[i] = false;
                }
                Answer::Refused => {}
            }
        }
    }
    Some(())
}

/// Builds witnesses in `s` by event-driven Horn propagation for members of `members` whose
/// group judged them `Inhabited`: one slot for a value of each node and one for a nonflat
/// value of it, one rule per way a node's value is built from its operands' values.
// Complexity tradeoff: with `N` nodes in the group's bodies (the shared `rec::Node` DAG) and
// `P` premises over all rules (at most the total arity, O(N)), each slot is seeded and popped
// once and each premise decremented once, O(N + P) hash and queue steps, plus one `s.rep` per
// closed node and one `s.show` per rule fired. Method: the linear-time Horn satisfiability
// algorithm of Dowling and Gallier (1984), one counter of unmet premises per rule. Naive
// alternative (XR-group-order-5 round 2, g2): build plain values and test each with
// `member_known`, which walks the value and took Θ(n³) (over 60 s) on a chain of n members
// whose values nest.
fn horn_witness_group(members: &[Type], s: &mut Search) {
    enum Action {
        Id,
        Tuple(usize),
        Atom(std::sync::Arc<str>, usize),
        DiffNf(usize),
        Closure(Morphism),
    }
    struct Rule {
        premises: Vec<usize>,
        rem: usize,
        out_inh: Option<usize>,
        out_nf: Option<usize>,
        action: Action,
    }

    let Some(first) = members.first() else {
        return;
    };
    let Node::Rec(r) = &*first.0 else {
        return;
    };
    let Some((env, _)) = r.key.member_at() else {
        return;
    };
    let bodies = &env.group().0.bodies;
    let n = bodies.len();
    if n != members.len() {
        return;
    }

    // Slots `0..n` are `inh(member i)`; slots `n..2*n` are `nf(member i)`.
    let mut vals: Vec<Option<usize>> = vec![None; 2 * n];
    // For `DiffNf` auxiliary slots: which component `j` supplied the non-flat witness.
    let mut nf_choice: HashMap<usize, (usize, usize)> = HashMap::new();
    let mut rules: Vec<Rule> = Vec::new();
    let mut watchers: Vec<Vec<usize>> = vec![Vec::new(); 2 * n];
    // Direct `DiffNf` component watchers: slot -> list of `(aux_slot, comp_index)`.
    let mut nf_arm_watchers: Vec<Vec<(usize, usize)>> = vec![Vec::new(); 2 * n];
    let mut queue: std::collections::VecDeque<(usize, usize)> = std::collections::VecDeque::new();

    let alloc_slot = |vals: &mut Vec<Option<usize>>,
                      watchers: &mut Vec<Vec<usize>>,
                      nf_arm_watchers: &mut Vec<Vec<(usize, usize)>>|
     -> usize {
        let id = vals.len();
        vals.push(None);
        watchers.push(Vec::new());
        nf_arm_watchers.push(Vec::new());
        id
    };

    let seed_slot = |slot: usize,
                     rep: usize,
                     vals: &mut [Option<usize>],
                     queue: &mut std::collections::VecDeque<(usize, usize)>| {
        if vals[slot].is_none() {
            vals[slot] = Some(rep);
            queue.push_back((slot, rep));
        }
    };

    for (i, m) in members.iter().enumerate() {
        if let Some(Some(rep)) = s.reps.get(m).copied() {
            seed_slot(i, rep, &mut vals, &mut queue);
            let loc = s.local(rep);
            let is_nf = match &s.shown[loc] {
                Rep::Value(v) => match v {
                    Value::Atom(a) => !a.is_bare(),
                    Value::Tuple(xs) => !xs.is_empty(),
                    _ => false,
                },
                Rep::Tuple(vs) => !vs.is_empty(),
                Rep::Atom(..) | Rep::Closure(_) => true,
                Rep::List { len, .. } => *len != BigUint::ZERO,
                Rep::Struct | Rep::Of { .. } => false,
            };
            if is_nf {
                seed_slot(n + i, rep, &mut vals, &mut queue);
            }
        }
    }

    let mut eval_cache: HashMap<u32, Type> = HashMap::new();
    let mut eval_cached = |node: &Arc<rec::Node>| -> Type {
        eval_cache
            .entry(node.class)
            .or_insert_with(|| eval(node, env))
            .clone()
    };

    enum Step<'a> {
        Visit(&'a Arc<rec::Node>),
        Make(&'a Arc<rec::Node>, usize),
    }
    let mut seen: HashMap<u32, (usize, usize)> = HashMap::new();
    let mut todo: Vec<Step<'_>> = Vec::new();
    let mut done: Vec<(usize, usize)> = Vec::new();

    let add_rule = |premises: Vec<usize>,
                    out_inh: Option<usize>,
                    out_nf: Option<usize>,
                    action: Action,
                    rules: &mut Vec<Rule>,
                    watchers: &mut [Vec<usize>]| {
        let rid = rules.len();
        let mut unique_p = premises.clone();
        unique_p.sort_unstable();
        unique_p.dedup();
        let rem = unique_p.len();
        for &p in &unique_p {
            watchers[p].push(rid);
        }
        rules.push(Rule {
            premises,
            rem,
            out_inh,
            out_nf,
            action,
        });
    };

    for (def, body) in bodies.iter().enumerate() {
        if members[def].judged() != Some(false) {
            continue;
        }
        todo.push(Step::Visit(body));
        while let Some(step) = todo.pop() {
            match step {
                Step::Visit(e) => {
                    let root = Arc::ptr_eq(e, body);
                    if let rec::Shape::Ref(i, _) = e.e {
                        let pair = (i, n + i);
                        if root {
                            add_rule(
                                vec![pair.0],
                                Some(def),
                                None,
                                Action::Id,
                                &mut rules,
                                &mut watchers,
                            );
                            add_rule(
                                vec![pair.1],
                                None,
                                Some(n + def),
                                Action::Id,
                                &mut rules,
                                &mut watchers,
                            );
                        } else {
                            done.push(pair);
                        }
                        continue;
                    }
                    if let Some(&pair) = seen.get(&e.class) {
                        if root {
                            add_rule(
                                vec![pair.0],
                                Some(def),
                                None,
                                Action::Id,
                                &mut rules,
                                &mut watchers,
                            );
                            add_rule(
                                vec![pair.1],
                                None,
                                Some(n + def),
                                Action::Id,
                                &mut rules,
                                &mut watchers,
                            );
                        } else {
                            done.push(pair);
                        }
                        continue;
                    }
                    if !e.recursive {
                        let s_inh = alloc_slot(&mut vals, &mut watchers, &mut nf_arm_watchers);
                        let s_nf = alloc_slot(&mut vals, &mut watchers, &mut nf_arm_watchers);
                        let t = eval_cached(e);
                        let operand_empty = match &e.e {
                            rec::Shape::Diff(a, _) => eval_cached(a).verdict() == Verdict::Empty,
                            rec::Shape::And(xs) => xs
                                .iter()
                                .any(|x| eval_cached(x).verdict() == Verdict::Empty),
                            _ => false,
                        };
                        if !operand_empty {
                            if let Some(r_inh) = s.rep(&t) {
                                seed_slot(s_inh, r_inh, &mut vals, &mut queue);
                            }
                            let nf_t = nonflat_part(&t);
                            if let Some(r_nf) = s.rep(&nf_t) {
                                seed_slot(s_nf, r_nf, &mut vals, &mut queue);
                            }
                        }
                        seen.insert(e.class, (s_inh, s_nf));
                        if root {
                            add_rule(
                                vec![s_inh],
                                Some(def),
                                None,
                                Action::Id,
                                &mut rules,
                                &mut watchers,
                            );
                            add_rule(
                                vec![s_nf],
                                None,
                                Some(n + def),
                                Action::Id,
                                &mut rules,
                                &mut watchers,
                            );
                        } else {
                            done.push((s_inh, s_nf));
                        }
                        continue;
                    }
                    match &e.e {
                        rec::Shape::Morphism(l, u, val)
                            if !l.recursive && !u.recursive && val.recursive =>
                        {
                            let (lt, ut) = (eval_cached(l), eval_cached(u));
                            if lt.subtype_verdict(&ut) == Verdict::Empty {
                                if lt.verdict() == Verdict::Empty {
                                    let s_inh =
                                        alloc_slot(&mut vals, &mut watchers, &mut nf_arm_watchers);
                                    let t = eval_cached(e);
                                    if let Some(r_mor) = s.rep(&t) {
                                        seed_slot(s_inh, r_mor, &mut vals, &mut queue);
                                    }
                                    seen.insert(e.class, (s_inh, s_inh));
                                    if root {
                                        add_rule(
                                            vec![s_inh],
                                            Some(def),
                                            Some(n + def),
                                            Action::Id,
                                            &mut rules,
                                            &mut watchers,
                                        );
                                    } else {
                                        done.push((s_inh, s_inh));
                                    }
                                } else if lt.verdict() == Verdict::Inhabited {
                                    todo.push(Step::Make(e, 1));
                                    todo.push(Step::Visit(val));
                                } else {
                                    let s_inh =
                                        alloc_slot(&mut vals, &mut watchers, &mut nf_arm_watchers);
                                    seen.insert(e.class, (s_inh, s_inh));
                                    if !root {
                                        done.push((s_inh, s_inh));
                                    }
                                }
                            } else {
                                let s_inh =
                                    alloc_slot(&mut vals, &mut watchers, &mut nf_arm_watchers);
                                seen.insert(e.class, (s_inh, s_inh));
                                if !root {
                                    done.push((s_inh, s_inh));
                                }
                            }
                        }
                        rec::Shape::Morphism(..) => {
                            let s_inh = alloc_slot(&mut vals, &mut watchers, &mut nf_arm_watchers);
                            let t = eval_cached(e);
                            if let Some(r_mor) = s.rep(&t) {
                                seed_slot(s_inh, r_mor, &mut vals, &mut queue);
                            }
                            seen.insert(e.class, (s_inh, s_inh));
                            if root {
                                add_rule(
                                    vec![s_inh],
                                    Some(def),
                                    Some(n + def),
                                    Action::Id,
                                    &mut rules,
                                    &mut watchers,
                                );
                            } else {
                                done.push((s_inh, s_inh));
                            }
                        }
                        rec::Shape::Union(xs)
                        | rec::Shape::Tuple(xs)
                        | rec::Shape::Atom(_, xs)
                        | rec::Shape::And(xs) => {
                            todo.push(Step::Make(e, xs.len()));
                            todo.extend(xs.iter().rev().map(Step::Visit));
                        }
                        rec::Shape::Diff(a, _) => {
                            todo.push(Step::Make(e, 1));
                            todo.push(Step::Visit(a));
                        }
                        _ => {
                            let s_inh = alloc_slot(&mut vals, &mut watchers, &mut nf_arm_watchers);
                            if !root {
                                done.push((s_inh, s_inh));
                            }
                        }
                    }
                }
                Step::Make(e, k) => {
                    let root = Arc::ptr_eq(e, body);
                    let parts = done.split_off(done.len() - k);
                    let s_inh = if root {
                        def
                    } else {
                        alloc_slot(&mut vals, &mut watchers, &mut nf_arm_watchers)
                    };
                    let s_nf = if root {
                        n + def
                    } else {
                        alloc_slot(&mut vals, &mut watchers, &mut nf_arm_watchers)
                    };
                    match &e.e {
                        rec::Shape::Union(_) => {
                            for &(pi, pnf) in &parts {
                                add_rule(
                                    vec![pi],
                                    Some(s_inh),
                                    None,
                                    Action::Id,
                                    &mut rules,
                                    &mut watchers,
                                );
                                add_rule(
                                    vec![pnf],
                                    None,
                                    Some(s_nf),
                                    Action::Id,
                                    &mut rules,
                                    &mut watchers,
                                );
                            }
                        }
                        rec::Shape::Tuple(xs) => {
                            if xs.is_empty() {
                                let unit_rep = s.show(Rep::Tuple(vec![]));
                                seed_slot(s_inh, unit_rep, &mut vals, &mut queue);
                            } else {
                                let inhs: Vec<usize> = parts.iter().map(|p| p.0).collect();
                                add_rule(
                                    inhs,
                                    Some(s_inh),
                                    Some(s_nf),
                                    Action::Tuple(xs.len()),
                                    &mut rules,
                                    &mut watchers,
                                );
                            }
                        }
                        rec::Shape::Atom(name, xs) => {
                            if xs.is_empty() {
                                let t = eval_cached(e);
                                if let Some(bare_rep) = s.rep(&t) {
                                    seed_slot(s_inh, bare_rep, &mut vals, &mut queue);
                                }
                            } else {
                                let inhs: Vec<usize> = parts.iter().map(|p| p.0).collect();
                                add_rule(
                                    inhs,
                                    Some(s_inh),
                                    Some(s_nf),
                                    Action::Atom(name.as_str().into(), xs.len()),
                                    &mut rules,
                                    &mut watchers,
                                );
                            }
                        }
                        rec::Shape::Morphism(..) => {
                            let t = eval_cached(e);
                            let mut found_m = None;
                            let mut seen_m = DigestSet::default();
                            t.p().morphisms.taken_toward(true, &mut seen_m, &mut |m| {
                                if found_m.is_none() {
                                    found_m = Some(m.clone());
                                }
                            });
                            if let Some(m_mor) = found_m {
                                add_rule(
                                    vec![parts[0].0],
                                    Some(s_inh),
                                    Some(s_nf),
                                    Action::Closure(m_mor),
                                    &mut rules,
                                    &mut watchers,
                                );
                            }
                        }
                        rec::Shape::And(xs) => {
                            let tys: Vec<Type> = xs.iter().map(&mut eval_cached).collect();
                            if !disjoint_top_carriers(&tys) {
                                let mut rec_keys = BTreeSet::new();
                                let mut closed_meet = Type::top();
                                let mut rec_idx = None;
                                for (idx, x) in xs.iter().enumerate() {
                                    if x.recursive {
                                        let key = match &x.e {
                                            rec::Shape::Ref(i, a) if a.is_empty() => {
                                                (0u8, *i as u32)
                                            }
                                            _ => (1u8, x.class),
                                        };
                                        rec_keys.insert(key);
                                        rec_idx = Some(idx);
                                    } else {
                                        closed_meet = &closed_meet & &tys[idx];
                                    }
                                }
                                if rec_keys.len() == 1
                                    && let Some(idx) = rec_idx
                                {
                                    if closed_meet == Type::top() {
                                        add_rule(
                                            vec![parts[idx].0],
                                            Some(s_inh),
                                            None,
                                            Action::Id,
                                            &mut rules,
                                            &mut watchers,
                                        );
                                        add_rule(
                                            vec![parts[idx].1],
                                            None,
                                            Some(s_nf),
                                            Action::Id,
                                            &mut rules,
                                            &mut watchers,
                                        );
                                    } else if is_flat_type(&closed_meet)
                                        && let Some(xf) = flat_part(&tys[idx])
                                        && let Some(rep) = s.rep(&(&xf & &closed_meet))
                                    {
                                        seed_slot(s_inh, rep, &mut vals, &mut queue);
                                    }
                                }
                            }
                        }
                        rec::Shape::Diff(a, r) => {
                            let r_ty = eval_cached(r);
                            let r_empty = match &r.e {
                                rec::Shape::Diff(ra, _) if !r.recursive => {
                                    eval_cached(ra).verdict() == Verdict::Empty
                                }
                                rec::Shape::And(rxs) if !r.recursive => rxs
                                    .iter()
                                    .any(|x| eval_cached(x).verdict() == Verdict::Empty),
                                _ => false,
                            };
                            if r_empty || r_ty.verdict() == Verdict::Empty {
                                add_rule(
                                    vec![parts[0].0],
                                    Some(s_inh),
                                    None,
                                    Action::Id,
                                    &mut rules,
                                    &mut watchers,
                                );
                                add_rule(
                                    vec![parts[0].1],
                                    None,
                                    Some(s_nf),
                                    Action::Id,
                                    &mut rules,
                                    &mut watchers,
                                );
                            } else if is_flat_type(&r_ty) {
                                if let Some(af) = flat_part(&eval_cached(a))
                                    && let Some(rep) = s.rep(&(&af - &r_ty))
                                {
                                    seed_slot(s_inh, rep, &mut vals, &mut queue);
                                }
                                add_rule(
                                    vec![parts[0].1],
                                    Some(s_inh),
                                    Some(s_nf),
                                    Action::Id,
                                    &mut rules,
                                    &mut watchers,
                                );
                            } else if let rec::Shape::Tuple(xs) = &a.e
                                && !xs.is_empty()
                            {
                                let xs_tys: Vec<Type> = xs.iter().map(&mut eval_cached).collect();
                                if let Some(r_ty_m) = flat_tuple_subtrahend(&r_ty, &xs_tys) {
                                    let flats: Option<Vec<Type>> =
                                        xs_tys.iter().map(flat_part).collect();
                                    let mut seeded = false;
                                    if let Some(flats) = flats
                                        && let Some(rep) = s.rep(&(&Type::tuple(flats) - &r_ty_m))
                                    {
                                        seed_slot(s_inh, rep, &mut vals, &mut queue);
                                        seed_slot(s_nf, rep, &mut vals, &mut queue);
                                        seeded = true;
                                    }
                                    if !seeded {
                                        let aux_nf = alloc_slot(
                                            &mut vals,
                                            &mut watchers,
                                            &mut nf_arm_watchers,
                                        );
                                        let mut premises = Vec::with_capacity(xs.len() + 1);
                                        for (j, x) in xs.iter().enumerate() {
                                            let xp = match &x.e {
                                                rec::Shape::Ref(i, _) => (*i, n + *i),
                                                _ => match seen.get(&x.class) {
                                                    Some(&p) => p,
                                                    None => continue,
                                                },
                                            };
                                            premises.push(xp.0);
                                            nf_arm_watchers[xp.1].push((aux_nf, j));
                                        }
                                        if premises.len() == xs.len() {
                                            premises.push(aux_nf);
                                            add_rule(
                                                premises,
                                                Some(s_inh),
                                                Some(s_nf),
                                                Action::DiffNf(xs.len()),
                                                &mut rules,
                                                &mut watchers,
                                            );
                                        }
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                    seen.insert(e.class, (s_inh, s_nf));
                    if !root {
                        done.push((s_inh, s_nf));
                    }
                }
            }
        }
    }

    // Propagate to the least fixed point. `add_rule` set each rule's `rem` to its number of
    // distinct premises and no slot has been popped yet, so every seeded slot (seeded during
    // construction or later) is popped exactly once and decrements each rule that reads it:
    // a rule fires if and only if all its premises are seeded. Cost: O(premises + slots).
    while let Some((slot, rep)) = queue.pop_front() {
        let arms = std::mem::take(&mut nf_arm_watchers[slot]);
        for (aux, j) in arms {
            if let Entry::Vacant(e) = nf_choice.entry(aux) {
                e.insert((j, rep));
                seed_slot(aux, rep, &mut vals, &mut queue);
            }
        }
        let rids = std::mem::take(&mut watchers[slot]);
        for rid in rids {
            if rules[rid].rem == 0 {
                continue;
            }
            rules[rid].rem -= 1;
            if rules[rid].rem == 0 {
                let built = match &rules[rid].action {
                    Action::Id => vals[rules[rid].premises[0]],
                    Action::Tuple(m) => {
                        let vs: Vec<usize> = rules[rid].premises[..*m]
                            .iter()
                            .map(|&p| vals[p].expect("ready"))
                            .collect();
                        Some(s.show(Rep::Tuple(vs)))
                    }
                    Action::Atom(name, m) => {
                        let vs: Vec<usize> = rules[rid].premises[..*m]
                            .iter()
                            .map(|&p| vals[p].expect("ready"))
                            .collect();
                        let tup = s.show(Rep::Tuple(vs));
                        Some(s.show(Rep::Atom(name.clone(), tup)))
                    }
                    Action::DiffNf(m) => {
                        let aux = rules[rid].premises[*m];
                        nf_choice.get(&aux).map(|&(j_nf, rep_nf)| {
                            let mut vs: Vec<usize> = rules[rid].premises[..*m]
                                .iter()
                                .map(|&p| vals[p].expect("ready"))
                                .collect();
                            vs[j_nf] = rep_nf;
                            s.show(Rep::Tuple(vs))
                        })
                    }
                    Action::Closure(m_mor) => Some(s.show(Rep::Closure(m_mor.clone()))),
                };
                if let Some(new_rep) = built {
                    if let Some(oi) = rules[rid].out_inh {
                        seed_slot(oi, new_rep, &mut vals, &mut queue);
                    }
                    if let Some(onf) = rules[rid].out_nf {
                        seed_slot(onf, new_rep, &mut vals, &mut queue);
                    }
                }
            }
        }
    }

    // Each value in `vals` is in its slot's type by the rule that built it: every rule above
    // builds a value of its node from values of its operands (a tuple or atom from its
    // components, a union from an arm, a meet from its one recursive conjunct when the others
    // are `top` (`rec_keys`), a difference from a value outside a flat subtrahend, a nonflat
    // component taking the tuple outside it), so a member's value is in the least fixed point.
    // It is kept with no test: a test by `member_known` walks the value against every member,
    // Θ(n²) for a chain of n members whose values nest.
    for (i, m) in members.iter().enumerate() {
        if s.reps.get(m).is_some_and(Option::is_some) {
            continue;
        }
        if let Some(rep) = vals[i] {
            let c = s.class(rep);
            s.members.insert((c, m.clone()), Some(true));
            s.reps.insert(m.clone(), Some(rep));
        }
    }
}

/// Whether any body of `env`'s group mentions `&` or `\`.
fn group_has_diff_or_and(env: &Arc<Env>) -> bool {
    let mut stack: Vec<&rec::Node> = env.group().0.bodies.iter().map(|b| &**b).collect();
    let mut seen: HashSet<u32> = HashSet::new();
    while let Some(n) = stack.pop() {
        if !seen.insert(n.class) {
            continue;
        }
        match &n.e {
            rec::Shape::And(_) | rec::Shape::Diff(..) => return true,
            rec::Shape::Union(xs) | rec::Shape::Tuple(xs) | rec::Shape::Atom(_, xs) => {
                stack.extend(xs.iter().map(|c| &**c));
            }
            rec::Shape::Morphism(l, u, v) => stack.extend([&**l, &**u, &**v]),
            rec::Shape::Not(a) => stack.push(a),
            rec::Shape::Param(_) | rec::Shape::Type(_) | rec::Shape::Ref(..) => {}
        }
    }
    false
}

/// A node's emptiness from its answers with the leaves `Bot` (`low`) and `Top` (`high`), when
/// they decide it: empty when empty with the leaves `Top`, inhabited when inhabited with them
/// `Bot` and the node reaches no meet or difference (`wide`), whose operands hold more values
/// than it.
fn settled(low: Answer, high: Answer, wide: bool) -> Option<bool> {
    match (low, high) {
        (_, Answer::Empty) => Some(true),
        (Answer::Inhabited, _) if !wide => Some(false),
        _ => None,
    }
}

/// The systems of a group's types beside `b`, for [`judge`]. First `b` with each union of one
/// distinct arm read as that arm ([`names::contracted`]), as a member whose body is a name; then
/// that less the arms a union also reaches through names ([`names::absorb`]); and each of the two
/// with the nodes that play alike merged ([`names::merged`]), and that less the arms the merged
/// copy shows a union also reaches. Merging after the drop decides parts that play alike only
/// once a union's arm is dropped (item GROUP-arm-drop-merge). Each is decided with its leaves
/// `Bot` and, when it has leaves, `Top`.
struct Others {
    /// Each system's runs, and which of `maps` takes `b`'s nodes to its nodes, if any.
    runs: Vec<(Decision, Option<Decision>, Option<usize>)>,
    /// For each system with nodes of its own, its node for each node of `b`.
    maps: Vec<Vec<u32>>,
}

impl Others {
    /// The systems of `b`, whose `leaves` are `Top` on entry and on return; `same` and `union`
    /// as [`System`] gives them.
    fn new(b: &mut Bes, leaves: &[u32], same: &[u32], union: &[bool]) -> Others {
        // `absorb` and `merged` read the leaves `Bot`, as `system` made them.
        for &v in leaves {
            b.set(v, Kind::Bot, vec![]);
        }
        let mut systems: Vec<(Bes, Vec<u32>, Option<usize>)> = Vec::new();
        let mut maps = Vec::new();
        let mut leaf = vec![false; b.len()];
        for &v in leaves {
            leaf[v as usize] = true;
        }
        // `b` with each union of one distinct arm read as that arm (`base`), so that a member
        // whose body is a name is no second union over the member it names; `at` the place in
        // `maps` of its node for each node of `b`, with its types, unions, leaves.
        let mut contracted = names::contracted(b);
        let (at, base_same, base_union, base_leaf, base_leaves) = match contracted.as_mut() {
            None => (None, Vec::new(), Vec::new(), Vec::new(), Vec::new()),
            Some((_, to, kept)) => {
                let mut ls: Vec<u32> = leaves.iter().map(|&v| to[v as usize]).collect();
                ls.sort_unstable();
                ls.dedup();
                let pick = |v: &u32| (same[*v as usize], union[*v as usize], leaf[*v as usize]);
                let (s, (u, l)): (Vec<u32>, (Vec<bool>, Vec<bool>)) =
                    kept.iter().map(pick).map(|(s, u, l)| (s, (u, l))).unzip();
                maps.push(std::mem::take(to));
                (Some(0), s, u, l, ls)
            }
        };
        let (base, same, union, leaf, leaves_of_base): (&Bes, &[u32], &[bool], &[bool], &[u32]) =
            match &contracted {
                None => (&*b, same, union, &leaf, leaves),
                Some((c, _, _)) => (c, &base_same, &base_union, &base_leaf, &base_leaves),
            };
        let dropped = names::absorb(base, same, union);
        // `base`, and `base` less the arms `absorb` drops, which has `base`'s nodes, leaves and
        // unions, each merged and then less the arms that the merged copy shows a union also
        // reaches.
        let mut base_merged = false;
        for (k, g) in std::iter::once(base).chain(dropped.as_ref()).enumerate() {
            if let Some((m, node, union)) = names::merged(g, leaf, union) {
                base_merged |= k == 0;
                let node: Vec<u32> = match at {
                    Some(j) => maps[j].iter().map(|&v: &u32| node[v as usize]).collect(),
                    None => node,
                };
                let mut leaves: Vec<u32> = leaves.iter().map(|&v| node[v as usize]).collect();
                leaves.sort_unstable();
                leaves.dedup();
                let types: Vec<u32> = (0..m.len() as u32).collect();
                if let Some(a) = names::absorb(&m, &types, &union) {
                    systems.push((a, leaves.clone(), Some(maps.len())));
                }
                systems.push((m, leaves, Some(maps.len())));
                maps.push(node);
            }
        }
        if let Some(a) = dropped {
            systems.push((a, leaves_of_base.to_vec(), at));
        }
        // `base` itself, when it is not `b` and no merged copy stands for it.
        if let Some((c, _, _)) = contracted.filter(|_| !base_merged) {
            systems.push((c, base_leaves, at));
        }
        for &v in leaves {
            b.set(v, Kind::Top, vec![]);
        }
        let runs = (systems.into_iter())
            .map(|(mut g, leaves, map)| {
                let low = decide(&g);
                let high = (!leaves.is_empty()).then(|| {
                    // A leaf has no children either way, so the parents `seal` filled stay right.
                    for &v in &leaves {
                        g.set(v, Kind::Top, vec![]);
                    }
                    decide(&g)
                });
                (low, high, map)
            })
            .collect();
        Others { runs, maps }
    }

    /// Member `i`'s emptiness by each system that settles it; `wide` as for [`settled`].
    fn answers(&self, i: usize, wide: bool) -> impl Iterator<Item = bool> + '_ {
        self.runs.iter().filter_map(move |(low, high, map)| {
            let high = high.as_ref().unwrap_or(low);
            let v = map.map_or(i, |k| self.maps[k][i] as usize);
            settled(low.answers[v], high.answers[v], wide)
        })
    }
}

impl Why {
    /// What the messages of the refused members of a group read: the decider's system `graph`,
    /// the definition and expression of each node (`origin`), its runs and which nodes reach a
    /// meet or a difference (`wide`), with which nodes reach a refused node. Time linear in the
    /// system.
    fn new(
        members: usize,
        graph: Bes,
        origin: Vec<(usize, Arc<rec::Node>)>,
        meets: HashMap<u32, Vec<u32>>,
        runs: Vec<Decision>,
        wide: Vec<bool>,
    ) -> Why {
        let of = (runs.iter())
            .map(|d| {
                (d.refusals.iter().enumerate())
                    .flat_map(|(k, c)| c.component.iter().map(move |&v| (v, k)))
                    .collect()
            })
            .collect();
        // The nodes that reach a refused node: those refused, then their parents, each once.
        let mut open: Vec<bool> = (0..graph.len())
            .map(|v| runs.iter().any(|d| d.answers[v] == Answer::Refused))
            .collect();
        let mut stack: Vec<u32> = (0..graph.len() as u32)
            .filter(|&v| open[v as usize])
            .collect();
        while let Some(v) = stack.pop() {
            for &u in graph.parents(v) {
                if !open[u as usize] {
                    open[u as usize] = true;
                    stack.push(u);
                }
            }
        }
        Why {
            members: members as u32,
            wide,
            graph,
            origin,
            meets,
            runs,
            of,
            open,
            checked: Mutex::new(HashMap::new()),
        }
    }
}

/// The decider's system of a group ([`judge`]), sealed: the definition and expression each
/// node stands for, by its number (the members' bodies first), the nodes of meets and
/// differences, the leaves, the parts the decider does not take, and each node's type across
/// the definitions and whether it is a union, which [`names::absorb`] reads.
struct System {
    b: Bes,
    origin: Vec<(usize, Arc<rec::Node>)>,
    /// Each meet's node, with the node of each of its operands as written in its origin, a
    /// recursive meet among them read as its own operands: its children before they are sorted.
    meets: HashMap<u32, Vec<u32>>,
    wider: Vec<u32>,
    leaves: Vec<u32>,
    same: Vec<u32>,
    union: Vec<bool>,
}

/// What a node of the system is made of, within one definition; parts of one definition with
/// one key get one node (item GROUP-cycle-dup).
#[derive(PartialEq, Eq, Hash)]
enum Made<'a> {
    /// A union, by the set of its arms' nodes, an arm that is itself a union read as its arms.
    Or(Vec<u32>),
    Tuple(Vec<u32>),
    Atom(&'a str, Vec<u32>),
    Meet(Vec<u32>),
    /// A difference, by its right operand's class and its left operand's node.
    Diff(u32, u32),
    /// A morphism type, by its bounds' classes and its value type's node.
    Mor(u32, u32, u32),
}

impl<'a> Made<'a> {
    /// The node's kind and children.
    fn node(self) -> (Kind, Vec<u32>) {
        match self {
            Made::Or(xs) => (Kind::Or, xs),
            Made::Tuple(xs) | Made::Atom(_, xs) | Made::Meet(xs) => (Kind::And, xs),
            Made::Diff(_, a) => (Kind::Or, vec![a]),
            Made::Mor(_, _, v) => (Kind::Mor, vec![v]),
        }
    }

    /// The same key with each child node replaced by its type's number in `same`, a union's
    /// arms again a set: the key of the type across the group's definitions.
    fn across(&self, same: &[u32]) -> Made<'a> {
        let map = |xs: &[u32]| xs.iter().map(|&x| same[x as usize]).collect::<Vec<u32>>();
        match self {
            Made::Or(xs) => {
                let mut ys = map(xs);
                ys.sort_unstable();
                ys.dedup();
                Made::Or(ys)
            }
            Made::Tuple(xs) => Made::Tuple(map(xs)),
            Made::Atom(name, xs) => Made::Atom(name, map(xs)),
            Made::Meet(xs) => {
                let mut ys = map(xs);
                ys.sort_unstable();
                ys.dedup();
                Made::Meet(ys)
            }
            Made::Diff(r, a) => Made::Diff(*r, same[*a as usize]),
            Made::Mor(l, u, v) => Made::Mor(*l, *u, same[*v as usize]),
        }
    }
}

/// What a type of a group's system is, across its definitions ([`names::absorb`]): a part
/// with children by what it is made of, its children read across definitions, and a part with
/// none by its class.
#[derive(PartialEq, Eq, Hash)]
enum Same<'a> {
    Made(Made<'a>),
    Class(u32),
}

/// The system of `env`'s group, read from the members' bodies: a node for each member, and one
/// for each part of a body that mentions the group, except that a recursive occurrence is the
/// member's own node, so the graph has the group's shape.
///
/// Parts of one definition written alike up to the order, repetition and grouping of union arms
/// are one node, and a union's arms are a set: `A | A` is `A`, `A | B` and `B | A` are one node,
/// and `(A | B) | C` has the arms `A`, `B` and `C`. The decider's refusal counts the independent
/// cycles of the graph as edges minus nodes plus one, and takes the exact path for a component
/// with one morphism type in it, so a node made for each arm as written made the verdict depend
/// on how a type is written: a decided group with an arm written twice could be refused (item
/// GROUP-cycle-dup). Merging two nodes with equal children, or lifting the arms of a union with
/// one parent into that parent, removes as many edges as nodes or more, so it never adds a cycle;
/// the answers are those of the types, which the merging does not change. A reference to
/// another definition stays that definition's node, so a union written through a definition's
/// name and the same union written out differ in their counts when the named union's arms
/// overlap the arms written beside it. Each node's type across the definitions (`same`) is
/// numbered for [`names::absorb`], which [`judge`] uses to decide a second system with those arms
/// dropped (item GROUP-cycle-dup-names). Parts of two definitions are not merged here, so each
/// node's origin, which the refusal message reads, is in the definition that wrote it; equal
/// parts of two definitions are merged in a copy that [`judge`] decides beside this system
/// ([`names::merged`], item GROUP-cycle-dup-across).
///
/// Each part is read once, from a stack; a part written like one met before in its definition
/// is not read again. Expected time linear in the bodies, besides sorting each union's arms and
/// the emptiness of the closed parts.
fn system(env: &Arc<Env>) -> System {
    enum Step<'a> {
        /// A part to read.
        Visit(&'a Arc<rec::Node>),
        /// A part whose children's nodes, as many as given, are the last on `done`.
        Make(&'a Arc<rec::Node>, usize),
    }
    let bodies = &env.group().0.bodies;
    let mut b = Bes::new();
    let mut origin = Vec::with_capacity(bodies.len());
    // Each node's type across the definitions, a member's its own number (`Same`), and
    // whether the node is a union, by its number.
    let (mut same, mut union) = (Vec::with_capacity(bodies.len()), vec![false; bodies.len()]);
    for (i, e) in bodies.iter().enumerate() {
        b.add(Kind::Bot, vec![]);
        origin.push((i, Arc::clone(e)));
        same.push(i as u32);
    }
    // The number of each type met, after the members'.
    let mut types: HashMap<Same<'_>, u32> = HashMap::new();
    let type_of = |types: &mut HashMap<_, _>, key| {
        let next = (bodies.len() + types.len()) as u32;
        *types.entry(key).or_insert(next)
    };
    let (mut wider, mut leaves) = (Vec::new(), Vec::new());
    // The node of each part read, by its definition and class.
    let mut seen: HashMap<(usize, u32), u32> = HashMap::new();
    // The nodes with children, by their definition and what they are made of; their children
    // are set from the keys once every node is made.
    let mut made: HashMap<(usize, Made<'_>), u32> = HashMap::new();
    let mut meets: HashMap<u32, Vec<u32>> = HashMap::new();
    let (mut todo, mut done, mut arms) = (Vec::new(), Vec::new(), Vec::new());
    for (def, body) in bodies.iter().enumerate() {
        todo.push(Step::Visit(body));
        while let Some(step) = todo.pop() {
            let (e, parts) = match step {
                Step::Visit(e) => {
                    let root = Arc::ptr_eq(e, body);
                    if let rec::Shape::Ref(i, _) = e.e {
                        if root {
                            b.set(def as u32, Kind::Or, vec![i as u32]);
                            union[def] = true;
                        } else {
                            done.push(i as u32);
                        }
                        continue;
                    }
                    if let Some(&v) = seen.get(&(def, e.class)) {
                        done.push(v);
                        continue;
                    }
                    // A closed part is read by its verdict, never by `is_empty`, whose
                    // "inhabited" may be a check that gave up: a member judged on it could be
                    // judged empty when it is not.
                    let childless = match &e.e {
                        _ if !e.recursive => match eval(e, env).verdict() {
                            Verdict::Empty => Some(Some(Kind::Bot)),
                            Verdict::Inhabited => Some(Some(Kind::Top)),
                            Verdict::Refused(_) => Some(None),
                        },
                        // Admitted only with equal bounds and a value type that is not empty.
                        rec::Shape::Morphism(l, u, val) if l.recursive || u.recursive => Some(
                            (!val.recursive && eval(val, env).verdict() == Verdict::Inhabited)
                                .then_some(Kind::Top),
                        ),
                        rec::Shape::Morphism(l, u, val) => {
                            let (l, u) = (eval(l, env), eval(u, env));
                            // A key promised and not permitted leaves no morphism; with no key
                            // promised the empty morphism is one.
                            match (l.subtype_verdict(&u), l.verdict()) {
                                (Verdict::Refused(_), _) | (_, Verdict::Refused(_)) => Some(None),
                                (Verdict::Inhabited, _) => Some(Some(Kind::Bot)),
                                (Verdict::Empty, Verdict::Empty) => Some(Some(Kind::Top)),
                                (Verdict::Empty, Verdict::Inhabited) => {
                                    todo.push(Step::Make(e, 1));
                                    todo.push(Step::Visit(val));
                                    None
                                }
                            }
                        }
                        rec::Shape::Union(xs) => {
                            // The arms, a union written as an arm read as its own arms.
                            let at = todo.len() + 1;
                            todo.push(Step::Make(e, 0));
                            arms.extend(xs.iter().rev());
                            while let Some(x) = arms.pop() {
                                match &x.e {
                                    rec::Shape::Union(ys) if x.recursive => {
                                        arms.extend(ys.iter().rev());
                                    }
                                    _ => todo.push(Step::Visit(x)),
                                }
                            }
                            let k = todo.len() - at;
                            todo[at - 1] = Step::Make(e, k);
                            None
                        }
                        rec::Shape::Tuple(xs) | rec::Shape::Atom(_, xs) => {
                            todo.push(Step::Make(e, xs.len()));
                            todo.extend(xs.iter().rev().map(Step::Visit));
                            None
                        }
                        rec::Shape::And(xs) => {
                            let at = todo.len() + 1;
                            todo.push(Step::Make(e, 0));
                            arms.extend(xs.iter().rev());
                            while let Some(x) = arms.pop() {
                                match &x.e {
                                    rec::Shape::And(ys) if x.recursive => {
                                        arms.extend(ys.iter().rev());
                                    }
                                    _ => todo.push(Step::Visit(x)),
                                }
                            }
                            let k = todo.len() - at;
                            todo[at - 1] = Step::Make(e, k);
                            None
                        }
                        rec::Shape::Diff(a, _) => {
                            todo.push(Step::Make(e, 1));
                            todo.push(Step::Visit(a));
                            None
                        }
                        rec::Shape::Not(_) => {
                            // Only a recursive part gets here (the first arm takes the rest).
                            // `Group::new`, the one maker of a group and so of its `Env`,
                            // rejects a group whose `flipped` finds a recursive `Not`, and
                            // `flipped` visits every node of every body.
                            unreachable!(
                                "admission keeps a recursive occurrence out of a complement"
                            )
                        }
                        rec::Shape::Param(_) | rec::Shape::Type(_) | rec::Shape::Ref(..) => {
                            // A `Ref` is taken at the top of `Step::Visit`; a `Param` or `Type`
                            // has no children, so it is not `recursive` (rec/group.rs, where
                            // `recursive` is set) and was taken by the first arm.
                            unreachable!("a closed part is not recursive")
                        }
                    };
                    let Some(kind) = childless else {
                        continue;
                    };
                    let v = if root {
                        def as u32
                    } else {
                        origin.push((def, Arc::clone(e)));
                        same.push(type_of(&mut types, Same::Class(e.class)));
                        union.push(false);
                        b.add(Kind::Bot, vec![])
                    };
                    match kind {
                        Some(kind) => b.set(v, kind, vec![]),
                        None => leaves.push(v),
                    }
                    if !root {
                        seen.insert((def, e.class), v);
                        done.push(v);
                    }
                    continue;
                }
                Step::Make(e, k) => (e, done.split_off(done.len() - k)),
            };
            let root = Arc::ptr_eq(e, body);
            // A meet's operands' nodes as written, kept where its origin is set.
            let mut written = None;
            let (key, wide) = match &e.e {
                rec::Shape::Union(_) => {
                    let mut parts = parts;
                    parts.sort_unstable();
                    parts.dedup();
                    if let [only] = parts[..]
                        && !root
                    {
                        seen.insert((def, e.class), only);
                        done.push(only);
                        continue;
                    }
                    (Made::Or(parts), false)
                }
                rec::Shape::Tuple(_) => (Made::Tuple(parts), false),
                rec::Shape::Atom(name, _) => (Made::Atom(name, parts), false),
                rec::Shape::And(_) => {
                    // The operands were pushed on `todo` in the order written, so they were
                    // visited, and their nodes put on `done`, in the reverse order.
                    written = Some(parts.iter().rev().copied().collect());
                    let mut parts = parts;
                    parts.sort_unstable();
                    parts.dedup();
                    (Made::Meet(parts), true)
                }
                rec::Shape::Diff(_, r) => (Made::Diff(r.class, parts[0]), true),
                rec::Shape::Morphism(l, u, _) => (Made::Mor(l.class, u.class, parts[0]), false),
                rec::Shape::Ref(..)
                | rec::Shape::Not(_)
                | rec::Shape::Param(_)
                | rec::Shape::Type(_) => {
                    // `Step::Make` is pushed only by the arms of `Step::Visit` for a morphism,
                    // a union, a tuple, an atom, a meet and a difference.
                    unreachable!("only a part with children is made after them")
                }
            };
            if root {
                union[def] = matches!(key, Made::Or(_));
                let (kind, children) = key.node();
                b.set(def as u32, kind, children);
                if wide {
                    wider.push(def as u32);
                }
                if let Some(w) = written {
                    meets.insert(def as u32, w);
                }
                continue;
            }
            let v = match made.entry((def, key)) {
                Entry::Occupied(o) => *o.get(),
                Entry::Vacant(slot) => {
                    let key = &slot.key().1;
                    same.push(type_of(&mut types, Same::Made(key.across(&same))));
                    union.push(matches!(key, Made::Or(_)));
                    let v = b.add(Kind::Bot, vec![]);
                    origin.push((def, Arc::clone(e)));
                    if wide {
                        wider.push(v);
                    }
                    if let Some(w) = written {
                        meets.insert(v, w);
                    }
                    *slot.insert(v)
                }
            };
            seen.insert((def, e.class), v);
            done.push(v);
        }
    }
    for ((_, key), v) in made {
        let (kind, children) = key.node();
        b.set(v, kind, children);
    }
    b.seal();
    System {
        b,
        origin,
        meets,
        wider,
        leaves,
        same,
        union,
    }
}

mod escape;
mod names;
mod refused;
mod shared;
mod sweep;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod bench;

fn carrier_root_order(members: &[Type]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..members.len()).collect();
    order.sort_by_key(|&i| match &*members[i].0 {
        Node::Rec(r) => u64::from(r.key.search_class()) + 1,
        Node::Parts(..) => 0,
    });
    order
}
