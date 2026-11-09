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
use std::hash::BuildHasherDefault;
use std::ops::{ControlFlow, Range};
use std::pin::Pin;
use std::sync::{Arc, Mutex};

use num_bigint::BigUint;

use super::bdd::{Bdd, Form, Part};
use super::bes::{Answer, Bes, Decision, Kind, decide};
use super::hash::KeyHasher;
use super::rec::unfold::eval;
use super::rec::{self, Env, Judgment, Why};
use super::{Held, Lits, Morphism, Node, Parts, Refusal, Row, Split, Type, Universes, Verdict};
use crate::frames::{Deep, Stack};
use crate::value::Value;

/// The hasher of the maps and sets keyed by types: a type hashes as its digest, made once when it
/// is built, so a lookup reads one node of the type, where a search of a `BTreeMap` compared the
/// key with some `log n` others, each comparison reading another node (EMPTY-morphism-next).
/// Equal digests are told apart by `Eq`, which compares contents.
type Digests = BuildHasherDefault<KeyHasher>;

/// A map keyed by types, hashed by their digests.
type ByType<V> = HashMap<Type, V, Digests>;

/// A set of types, hashed by their digests.
type TypeSet = HashSet<Type, Digests>;

thread_local! {
    static MEMO: RefCell<ByType<bool>> = const { RefCell::new(ByType::with_hasher(Digests::new())) };
    /// The verdict of each type asked. A verdict is decided by a search that reads no kept
    /// result, or with the other members of its recursive group ([`group_verdicts`]), so it is
    /// a function of the type alone, and keeping it changes no answer: these
    /// are the types proved empty and those with a checked value, and the refusals.
    static VERDICTS: RefCell<ByType<Verdict>> =
        const { RefCell::new(ByType::with_hasher(Digests::new())) };
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
    static STORES: RefCell<Vec<Vec<Rep>>> = const { RefCell::new(Vec::new()) };
    /// For each member given `Inhabited` by [`group_verdicts`] with a value its searches built:
    /// the list in `STORES` and the value's number there.
    static SHARED: RefCell<ByType<(usize, usize)>> =
        const { RefCell::new(ByType::with_hasher(Digests::new())) };
    /// The members of recursive groups this thread sent to the search of [`group_verdicts`]
    /// because their group's decider left them open ([`Type::members_searched`]).
    static SEARCHED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
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
    let open: Vec<Type> = (members.iter())
        .filter(|m| m.judged().is_none())
        .cloned()
        .collect();
    SEARCHED.with(|c| c.set(c.get() + open.len()));
    let mut d = Search {
        strict: true,
        refuse_forks: true,
        blame: Some(Vec::new()),
        ..Search::default()
    };
    let answers = d.solve_all(&open);
    let causes = d.causes();
    // For each member not decided by the decider, in order: whether the search proved it
    // empty, its number there, and the cause its answer may rest on. A fork met with no type
    // being decided ends the search, and refuses every root, as it does for one.
    let found: Vec<(bool, Option<usize>, Option<Refusal>)> = (open.iter().zip(answers))
        .map(|(m, b)| {
            let id = d.ids.get(m).copied();
            (b, id, d.refused.or(id.and_then(|i| causes[i])))
        })
        .collect();
    let mut found = found.into_iter();
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
    for m in members {
        let v = match m.judged() {
            Some(true) => Verdict::Empty,
            Some(false) if s.rep(m).is_some() => Verdict::Inhabited,
            // Complexity tradeoff: a member decided inhabited whose value the shared search does
            // not build gets a search of its own, which may read the whole group again; the X14
            // groups of 1024 and 2048 definitions measured for plan item VERDICT-group-share
            // needed none.
            Some(false) => m.verdict_alone(),
            None => {
                let (b, id, cause) = found.next().expect("one answer per member not decided");
                let decided = cause != Some(Refusal::Fork);
                if decided && b {
                    Verdict::Empty
                } else if decided
                    && (id.is_some_and(|i| d.witnessed.contains(&i)) || d.rep(m).is_some())
                    || s.rep(m).is_some()
                    || (o.get_or_insert_with(|| optimistic_values(members)).as_mut())
                        .is_some_and(|o| o.rep(m).is_some())
                {
                    Verdict::Inhabited
                } else {
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
                    Verdict::Refused(if m.refused_by_group() {
                        Refusal::Group
                    } else {
                        cause.or(d.gave_up).unwrap_or(Refusal::NoWitness)
                    })
                }
            }
        };
        VERDICTS.with(|k| k.borrow_mut().insert(m.clone(), v));
    }
    // The values built here, kept for the searches that read a member ([`Searching::shared`]):
    // a member shown inhabited by a value of the search for values, else of the first search,
    // else of the search in which each closure was taken to have a value.
    let mut o = o.flatten();
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
    DECIDING.with(|d| {
        let mut d = d.borrow_mut();
        for m in members {
            d.remove(m);
        }
    });
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
// build no value of. Tests: `l01_23_subtyping::group_oracle` (GROUP-closure-order).
fn optimistic_values(members: &[Type]) -> Option<Search> {
    let mut o = Search {
        strict: true,
        open_forks: true,
        optimistic: Some(Vec::new()),
        ..Search::default()
    };
    for m in members {
        o.rep(m);
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
        MEMO.with(|m| m.borrow_mut().clear());
        VERDICTS.with(|m| m.borrow_mut().clear());
        STORES.with(|m| m.borrow_mut().clear());
        SHARED.with(|m| m.borrow_mut().clear());
        super::rec::unfold::end_unit();
    }

    /// How many members of recursive groups this thread has sent to the search because their
    /// group's decider (module `bes`) left them open; a count that only grows, read by the tests
    /// to show which groups the decider settles with no search.
    pub fn members_searched() -> usize {
        SEARCHED.with(std::cell::Cell::get)
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
        self.judged()
    }

    /// Whether no value is in `self`, as far as the search proves it: a type it does not prove
    /// empty, as one whose search meets a fork, counts as inhabited.
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
        // Complexity tradeoff: a fork of recursive tuple types (`Searching::narrow_tuples`,
        // `Searching::tuples_on`) ends the search, and `self` counts as inhabited, as for
        // `Type::verdict`, which refuses it. Why: following both tuple types of a fork is the
        // subset construction, exponential in the recursive types (the lists of int against
        // lists with a 1 at each place from the end up to `n`: 8 ms, 277 ms and 32.5 s at `n`
        // 1, 4 and 6 when the search followed it). Trigger: a fork met in the search. Tests:
        // `l01_23_subtyping::refusals::emptiness_counts_a_fork_as_inhabited_in_its_size`.
        // COMPLEXITY.md K35. A complete solution needs the subset construction over the forked
        // tuple types; deciding whether such a union holds every list is NFA universality,
        // PSPACE-complete. The answers of a search a fork ended may rest on it, so none is kept.
        let mut s = Search {
            refuse_forks: true,
            ..Search::default()
        };
        let b = s.solve(self);
        if s.refused.is_some() {
            return false;
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
        let bare = p.atoms.cofinite || p.atoms.names.values().any(|a| a.bare);
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
            let inside: HashSet<usize> = roots.iter().map(Type::node_addr).collect();
            // Each node met, held for the walk, so that its address names no other node meanwhile.
            let mut seen: HashMap<usize, Type> =
                roots.iter().map(|t| (t.node_addr(), t.clone())).collect();
            let mut found = Vec::new();
            let mut stack: Vec<Type> = roots.to_vec();
            let visit = |t: &Type, seen: &mut HashMap<usize, Type>, stack: &mut Vec<Type>| {
                if let Entry::Vacant(v) = seen.entry(t.node_addr()) {
                    v.insert(t.clone());
                    stack.push(t.clone());
                }
            };
            while let Some(t) = stack.pop() {
                if let Some(g) = t.group().filter(|_| t.is_member())
                    && !inside.contains(&t.node_addr())
                {
                    if groups.insert(g) {
                        found.push(t);
                    }
                    continue;
                }
                let p = t.p();
                for a in p.atoms.names.values() {
                    visit(&a.payload, &mut seen, &mut stack);
                }
                p.tuples.atoms(&mut |row| {
                    row.iter().for_each(|x| visit(x, &mut seen, &mut stack));
                    true
                });
                p.morphisms.atoms(&mut |m| {
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
            // `l01_23_subtyping::refusals::each_refusal_names_its_cause` (`morphism_between`),
            // `l01_23_subtyping::witnesses::a_meet_of_cycles_is_shown_by_its_length` and
            // `l01_23_subtyping::judgments::a_morphism_cycle_through_an_empty_part_is_empty`.
            // COMPLEXITY.md Kept row "emptiness and subtyping of tuple and morphism parts". A
            // complete solution needs a value builder for every kind of type (closures included,
            // L2) and a complete search.
            Verdict::Refused(s.refused.or(s.gave_up).unwrap_or(Refusal::NoWitness))
        }
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
    ids: ByType<usize>,
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
    /// The values shown, each once, by number.
    shown: Vec<Rep>,
    /// The number here of each value of another search read ([`Rep::Of`]), by its list in
    /// `STORES` and its number there, so a value shared within that one is shared here too.
    foreign: HashMap<(usize, usize), usize>,
    /// For each such value whose parts were read in ([`Search::local`]), the number of the value
    /// made of them.
    expanded: HashMap<usize, usize>,
    members: HashMap<(usize, Type), Option<bool>, Digests>,
    /// Each type read as the value type of a morphism.
    value_reads: BTreeSet<usize>,
    /// Types proved empty for good: a morphism with such a value type has no value. All other
    /// value types read as inhabited, since a closure can return itself.
    dead: BTreeSet<usize>,
    /// The types being decided, on the stack: met for the first time, or decided again by
    /// [`Searching::drain`].
    deciding: BTreeSet<usize>,
    /// For each type, the types it read.
    reads: Vec<Vec<usize>>,
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
    /// is narrowed; set for the search of a value after a refused decision, which so follows
    /// no fork ([`Searching::tuples_on`]).
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
    blame: Option<Vec<(usize, Refusal)>>,
    /// Whether this is the first walk over the types, in which what a type read is on record.
    walking: bool,
    /// Whether values are sought only among the tuple types as written.
    seeding: bool,
    /// Key types with no value shown yet.
    keys: BTreeSet<Type>,
    /// What is known of each list type met, by the rule on pure cycles.
    cycles: ByType<Option<Cycle>>,
    /// The meet, difference or union of each pair of nodes the search built
    /// ([`Searching::cut`]), built once, by the nodes' addresses; the operands are kept with it,
    /// so no address is reused.
    cuts: HashMap<(usize, usize, Cut), (Type, Type, Type), Digests>,
    /// With a list, every closure whose keys are permitted as written is taken to have a value
    /// at once, and its value type is put on the list, to be shown to have a value after the
    /// search ([`optimistic_values`]).
    optimistic: Option<Vec<Type>>,
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
            return false;
        }
        if !new {
            return true;
        }
        for t in open {
            if !self.witnessed.contains(&t) {
                self.answer[t] = true;
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
        match (&mut self.blame, self.current) {
            (Some(blame), Some(c)) => blame.push((c, r)),
            _ if self.strict => {
                self.gave_up.get_or_insert(r);
            }
            _ => {}
        }
    }

    /// For a search with `blame`, the cause each type's answer may rest on: a fork met in the
    /// decision of a type it read, directly or through others, else the first part counted as
    /// inhabited with nothing shown in such a decision. Each type is marked once, by walks over
    /// the readers from the types blamed, forks first and then the rest in the order met:
    /// O(types + reads + blame).
    fn causes(&self) -> Vec<Option<Refusal>> {
        let mut cause = vec![None; self.types.len()];
        let blame = self.blame.as_deref().unwrap_or_default();
        let forks = blame.iter().filter(|(_, r)| *r == Refusal::Fork);
        let rest = blame.iter().filter(|(_, r)| *r != Refusal::Fork);
        let mut stack = Vec::new();
        for &(t, r) in forks.chain(rest) {
            if cause[t].is_some() {
                continue;
            }
            cause[t] = Some(r);
            stack.push(t);
            while let Some(x) = stack.pop() {
                for &y in &self.readers[x] {
                    if cause[y].is_none() {
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
    /// decided: an empty type read is what a proof rests on, and an inhabited one is not. Every
    /// type waiting to be decided again was decided first ([`Searching::no_value`]), so each
    /// answer read here is a decision of this phase, not the `true` a phase starts from. A
    /// type already dead changes nothing, so the phase that settles it again does not start
    /// another: each new phase takes at least one more type as dead, which bounds their number.
    fn settle(&mut self, v: usize) {
        if self.dead.contains(&v) {
            return;
        }
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
        for (a, root) in answers.iter_mut().zip(roots) {
            if root.p().atoms.names.is_empty() {
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
            if self.s().end_phase(open, new) {
                let s = self.s();
                return (answers.iter().zip(&ids))
                    .map(|(&b, id)| id.map_or(b, |r| s.answer[r]))
                    .collect();
            }
        }
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
                if !s.answer[t] {
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
            None => self.parts(&ty.p()).await,
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
                match (&mut s.blame, s.current) {
                    (Some(blame), Some(c)) => blame.push((c, Refusal::Fork)),
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
                    Morphism::new(Type::empty(), Type::top(), Type::top()),
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
        let t = self.cut(x, y, if both { Cut::Meet } else { Cut::Minus });
        self.empty(&t).await
    }

    /// `x op y`, built once per pair of nodes and kept in `cuts`, as for [`Searching::settles`]:
    /// the search reads the same morphism types again and again, and the meets and differences
    /// of their fields were built at each read, each a node of its own that `empty` then looked
    /// up by its contents (EMPTY-morphism-next). The tradeoff of keying by node is that of
    /// `settles`.
    fn cut(&self, x: &Type, y: &Type, op: Cut) -> Type {
        let key = (x.node_addr(), y.node_addr(), op);
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

    /// Notes a fork met in the decision of a verdict: against the type being decided in a search
    /// with several roots, else as the refusal that ends the search.
    fn refuse_fork(&self) {
        let mut guard = self.s();
        let s = &mut *guard;
        match (&mut s.blame, s.current) {
            (Some(blame), Some(c)) => blame.push((c, Refusal::Fork)),
            // Complexity tradeoff: a fork met while no type is being decided cannot be put on
            // the roots that read it, so it ends the search and refuses every root the decider
            // left open, as it refuses the one root of a search of its own. Trigger: `current`
            // is none at a fork. COMPLEXITY.md K61.
            _ => s.refused = Some(Refusal::Fork),
        }
    }

    /// Narrows the box and the part `f` to what `f` forces on it: a tuple type in every value
    /// of `f` meets the box, and a tuple type in none is taken out of the box when it holds the
    /// box in every component but one. True when `f` is proved empty on the box. Two tuple types
    /// it would take out of one component with different recursive types there, each on a
    /// cycle of its group, are a fork: the decision of a verdict refuses there, and the search
    /// of a value keeps that component.
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
            // `l01_23_subtyping::refusals::a_union_of_lists_by_the_place_of_a_one_is_refused_in_its_size`
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
                    // `l01_23_subtyping::refusals::a_union_of_lists_by_the_place_of_a_one_is_refused_in_its_size`
                    // and `a_value_found_by_refining_a_forked_part_is_kept`. COMPLEXITY.md K35.
                    // A complete solution needs the subset construction over the forked tuple
                    // types.
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
            let open: Vec<usize> = f.distinct_atoms().iter().map(|a| g.index[a]).collect();
            let forking = {
                let s = self.s();
                s.refuse_forks && !s.seeding
            };
            if forking && (0..g.r.len()).any(|j| g.forks(&open, j)) {
                // Complexity tradeoff: `verdict` refuses a part in which two open tuple types
                // differ in a recursive component on one box, instead of following both. Why:
                // following both is the subset construction, exponential in the recursive types
                // (hard by the reduction at the fork in `narrow_tuples`); `is_empty` stops here
                // too and counts the type as inhabited. A union of open tuple types less one
                // other, as `(P(6,4) | P(12,4))` less `P(3,1)` of lengths modulo periods, is
                // decided exactly by the split into the open tuple types below, but run before
                // this refusal the split is order `n` pieces by a part of `n` nodes on
                // `refusals::a_difference_of_forked_unions_is_refused_in_its_size` (62 times the
                // bytes at 8 times `n`; REFUSAL-nfa-refuse, not kept). Trigger: a
                // component on which the open tuple types fork, outside seeding. Tests:
                // `l01_23_subtyping::refusals::each_refusal_names_its_cause` (`fork_empty`) and
                // `a_value_is_sought_before_a_refusal` (`fork`). COMPLEXITY.md K26 and the Kept
                // row "emptiness and subtyping of tuple and morphism parts". A complete solution
                // needs the subset construction over the forked rows (a tree automaton
                // determinized on demand), exponential in the rows of the fork. A search with
                // several roots refuses only those that read the type being decided
                // (`Search::causes`).
                self.refuse_fork();
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
            // Complexity tradeoff: the one pass is tried only where the split below may follow,
            // not in that split's pieces, so a piece the pass would decide is left to the search
            // as before the pass. Why: each of the `k` pieces holds the whole part, and a pass
            // that gives no answer has still walked it, `k` walks in all (the choice chain
            // against a swapped one in `l01_23_subtyping::x13` grew 237 times in bytes at 8
            // times `d`, above its order `d²`). Trigger: `may_cover` false. COMPLEXITY.md K71.
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
                // below (`l01_23_subtyping::refusals::a_union_of_pairs_less_pairs_holding_them_is_empty_in_its_size`,
                // COMPLEXITY.md K80).
                if let Some(parts) = f.disjoint_disjuncts() {
                    for d in parts {
                        if !self.piece(g.r.clone(), d, true).await {
                            return false;
                        }
                    }
                    return true;
                }
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
            let held = Held::default();
            let groups = overlaps(cs.iter().map(|&c| g.cells[j][c].ty.p_held(&held)), &held);
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
        if p.structs || p.tuples.rest || !p.tuples.lens.is_empty() || !only_atoms(&p) {
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
    /// ([`group_verdicts`]), read here with no copy ([`Rep::Of`]), so each reader of a group does
    /// not build its values again. Each is a function of the group, whichever type asks first.
    /// Only a strict search reads it, as only one reads verdicts ([`Searching::group_verdict`]).
    fn shared(&'m self, t: &Type) -> Option<usize> {
        if !t.is_member() || !self.s().strict || DECIDING.with(|d| d.borrow().contains(t)) {
            return None;
        }
        if let Some(&r) = self.s().reps.get(t) {
            return r;
        }
        t.verdict();
        let (store, at) = SHARED.with(|m| m.borrow().get(t).copied())?;
        let mut s = self.s();
        let r = s.foreign(store, at, Some(t.clone()));
        s.reps.insert(t.clone(), Some(r));
        Some(r)
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
            return Stack::ready(Some(r));
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
                if !nested {
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
            let past = self.s().past_fork;
            let r = self.find_rep(&t).await;
            self.s().past_fork = past;
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
        if p.morphisms.is_leaf() != Some(false) {
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
            let meets: Vec<(Morphism, Vec<Type>)> = match (whole, p.morphisms.union_rows()) {
                (true, _) => vec![(
                    match taken.split_first() {
                        Some((a, rest)) => rest.iter().fold(a.clone(), |r, b| self.meet(&r, b)),
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
                (false, None) => Vec::new(),
            };
            for (m, keys) in &meets {
                if keys.iter().all(known_empty) {
                    return Some(self.s().show(Rep::Closure(m.clone())));
                }
                let permitted = m.guarantee == m.permission
                    || m.guarantee == Type::empty()
                    || m.permission == Type::top();
                if !permitted {
                    if self.no_keys(keys).await {
                        return Some(self.s().show(Rep::Closure(m.clone())));
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
                    return Some(self.s().show(Rep::Closure(m.clone())));
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
        let past = self.s().past_fork;
        for (len, whole) in &p.tuples.lens {
            if whole.union_rows().is_some() {
                continue;
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
            // (`l01_23_subtyping::refusals::a_union_of_forked_differences_is_refused_in_its_size`,
            // and `a_pair_type_met_with_forked_differences_is_refused_in_its_size`, whose pair
            // type holds the box and so drops out; COMPLEXITY.md K80).
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
                // `l01_23_subtyping::refusals::a_union_of_lists_by_the_place_of_a_one_is_refused_in_its_size`
                // and `a_value_is_sought_before_a_refusal` (`fork`, found by a candidate past
                // the first fork). COMPLEXITY.md K35. A complete solution needs the subset
                // construction over the forked tuple types.
                if self.s().kept_forks > forks {
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
                // One candidate for each tuple type left, narrowed by what the part says of it. A
                // candidate inside a tuple type the part excludes holds no value of it, and the
                // narrowing or the check of its row would say so, so it is skipped: narrowing it tests
                // every open cell of its components, n candidates by n cells, order n^2 types on the
                // pairs of `l01_23_subtyping::refusals::fork_by` (COMPLEXITY.md K35). So is a candidate
                // that lies inside an excluded tuple type in every component, as each pair of
                // `a_difference_of_forked_unions_is_refused_in_its_size` does (K80). `all_inside`
                // says whether every candidate was skipped so.
                let mut all_inside = true;
                for a in g.distinct_atoms() {
                    let k = b.index[&a];
                    if refused[k] || self.inside_excluded(&b, k, &sharing).await {
                        continue;
                    }
                    all_inside = false;
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
                // COMPLEXITY.md K80). A forked part not so proved empty is refined as before, so a
                // value only refining finds is kept (`a_value_found_by_refining_a_forked_part_is_kept`).
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
                if let Some(row) = self.refine(start, f).await
                    && let Some(v) = self.row_rep(&row, f).await
                {
                    return Some(v);
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
        let (j, classes) = classes(b, &open)?;
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
    /// step is at most two searches, so the searches are at most twice the tuple types times
    /// the components, and the box ends closed on every tuple type: the part then holds all of
    /// it or none.
    async fn refine(&'m self, start: Vec<Type>, f: &Part<Row>) -> Option<Vec<Type>> {
        let refuse_forks = std::mem::replace(&mut self.s().refuse_forks, false);
        let len = start.len();
        let mut g = self.region(start, f).await;
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
    /// `None` when that rests on the membership of a component that is not known. A tuple is
    /// in a tuple type when each component is in its own, and outside it when one component is
    /// surely outside its own, whichever component that is and whatever is not known of the
    /// others; `f` is then evaluated in three values ([`Part::eval3`]), so a tuple type whose
    /// membership is not known decides nothing only where `f`'s value rests on it. Neither
    /// depends on the order of the components (GROUP-closure-order: a closure whose membership
    /// is not known, met first, made the reversed tuple unknown where a later component was
    /// surely outside). A component is read by number when it is tested, so a tuple among the
    /// values shown is read in place while the tests add to the search.
    async fn holds_known(
        &'m self,
        item: impl Fn(&Search, usize) -> usize,
        f: &Part<Row>,
    ) -> Option<bool> {
        let mut known: BTreeMap<Row, Option<bool>> = BTreeMap::new();
        for a in f.distinct_atoms() {
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
            known.insert(a, fits);
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
                    Closure(Morphism, &'u Part<Morphism>),
                }
                let up = u.p();
                let shape = match &self.s().shown[v] {
                    Rep::Value(_) => unreachable!("a value was read above"),
                    Rep::Of { .. } => unreachable!("a value of another search was read in above"),
                    Rep::Closure(m) => match up.morphisms.is_leaf() {
                        Some(b) => Shape::Known(Some(b)),
                        None => Shape::Closure(m.clone(), &up.morphisms),
                    },
                    Rep::Struct => Shape::Known(Some(up.structs)),
                    Rep::Tuple(vs) => Shape::Tuple(up.tuples.get(vs.len())),
                    Rep::Atom(name, payload) => match up.atoms.names.get(name) {
                        None => Shape::Known(Some(up.atoms.cofinite)),
                        Some(a) => Shape::Payload(*payload, &a.payload),
                    },
                    Rep::List { item, .. } => Shape::List(*item),
                };
                match shape {
                    Shape::Known(b) => b,
                    Shape::Tuple(f) => self.holds_known(|s, i| s.tuple_item(v, i), &f).await,
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
    /// so membership is known only when every morphism type of `f` is `m`.
    fn closure_member(m: &Morphism, f: &Part<Morphism>) -> Option<bool> {
        let atoms = f.distinct_atoms();
        (atoms.iter().all(|a| a == m)).then(|| f.eval(&|a| a == m))
    }

    /// Whether every morphism `m` admits is in `n`, by the variance law. With no value, the
    /// empty morphism is the only one, and its domain is the guarantee.
    async fn within(&'m self, m: &Morphism, n: &Morphism) -> bool {
        let no_value = self.no_value(&m.value).await;
        self.settles(&n.guarantee, &m.guarantee, false).await
            && (no_value || self.settles(&m.permission, &n.permission, false).await)
            && (no_value
                || self.empty(&m.permission).await
                || self.settles(&m.value, &n.value, false).await)
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
                for a in f.distinct_atoms() {
                    let s = if inside.contains(&a) {
                        Some(true)
                    } else if self.no_morphism(&self.meet(&r, &a)).await {
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
                    r = taken.iter().fold(r, |r, a| self.meet(&r, a));
                    inside.extend(taken);
                    continue;
                }
                if may_cover && f.eval3(&|_| Some(false)) == Some(false) {
                    for a in f.distinct_atoms().iter() {
                        if !self.morphisms(self.meet(&r, a), f.clone(), false).await {
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
            let k = match p.view() {
                Ok(b) => Known {
                    leaf: Some((p, false)),
                    ..self.list(b)
                },
                Err(form) => match p.exclusive_or() {
                    Some((atoms, constant)) => Known {
                        leaf: Some((p, false)),
                        ..self.parity(&atoms, constant)
                    },
                    None => {
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
                            (_, None) => unreachable!("an `or` and an `and` have two operands"),
                        }
                    }
                },
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
            let form = match p.view() {
                Ok(_) => None,
                Err(form) => p.exclusive_or().is_none().then_some(form),
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
        if let Ok(b) = p.view() {
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
        let held = Held::default();
        let ps = cells.iter().map(|&c| g.cells[j][c].ty.p_held(&held));
        let groups = overlaps(ps, &held);
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
    /// The unfoldings of the recursive types met.
    held: &'a Held,
}

impl<'a> Walk<'a> {
    /// Puts the values of `t` under node `y`. A type met again adds nothing: met at another
    /// node, that node and the first are merged, so its keys under the first are its keys
    /// under both.
    fn enter(&mut self, trie: &mut Trie<'a>, y: usize, t: &'a Type) {
        match self.seen.entry(t) {
            Entry::Vacant(v) => {
                v.insert(y);
                self.todo.push((y, t.p_held(self.held)));
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
fn overlaps<'a>(ps: impl Iterator<Item = &'a Parts>, held: &'a Held) -> Vec<Vec<usize>> {
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
            held,
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
    if p.structs
        || p.tuples.rest
        || !p.tuples.lens.is_empty()
        || !only_atoms(&p)
        || p.atoms.cofinite
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
/// A union that names another union with some of the same arms is decided a second time with
/// those arms dropped ([`names::absorb`], item GROUP-cycle-dup-names), and a member decided by
/// either system is decided: both are systems of the same types. The refusal message reads the
/// first. Time linear in the bodies, besides the emptiness of their closed parts and the
/// O(m log m) of [`names::absorb`].
fn judge(env: &Arc<Env>) -> Judgment {
    let bodies = &env.group().0.bodies;
    let System {
        mut b,
        origin,
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
    let mut absorbed = names::absorb(&b, &same, &union);
    let mut runs = vec![decide(&b)];
    let mut also: Vec<Decision> = absorbed.iter().map(decide).collect();
    if !leaves.is_empty() {
        // A leaf has no children either way, so the parents `seal` filled stay right.
        for g in std::iter::once(&mut b).chain(absorbed.as_mut()) {
            for &v in &leaves {
                g.set(v, Kind::Top, vec![]);
            }
        }
        runs.push(decide(&b));
        also.extend(absorbed.iter().map(decide));
    }
    // Complexity tradeoff: a member shown inhabited through a meet or a difference goes to the
    // search, which builds a value of the meet: one state of the product of its operands per
    // node it reads. Why: the decider's answer is not exact there (`#a & #b`). Trigger: an
    // `Inhabited` answer on a node that reaches a meet or a difference. Cost: linear in the
    // meet's operands when a short value exists (`l01_23_subtyping::setop::meets_of_k_members_scale`,
    // 7.1 times at k 8 and 64); exponential when the search forks on the product, which the
    // verdict refuses as `Refusal::Fork` after a search for a value
    // (`the_product_of_k_parity_lists_is_refused_by_its_fork`: 178M, 1.11G and 4.51G
    // instructions at k 2, 3 and 4). COMPLEXITY.md K84. A complete solution needs the product
    // construction of the meet's tree automata, exponential in the number of operands
    // (emptiness of an intersection of tree automata is EXPTIME-complete).
    let n = bodies.len();
    let (mut answers, mut refused) = (vec![None; n], vec![false; n]);
    for i in 0..n {
        let (low, high) = (runs[0].answers[i], runs[runs.len() - 1].answers[i]);
        let named = settled(low, high, wide[i]);
        let read = (also.first().zip(also.last()))
            .and_then(|(first, last)| settled(first.answers[i], last.answers[i], wide[i]));
        debug_assert!(
            named.is_none() || read.is_none() || named == read,
            "the two systems of one group's types agree"
        );
        answers[i] = named.or(read);
        refused[i] = answers[i].is_none() && (low == Answer::Refused || high == Answer::Refused);
    }
    let why = refused
        .contains(&true)
        .then(|| Why::new(n, b, origin, runs, wide));
    Judgment {
        answers,
        refused,
        why,
    }
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

impl Why {
    /// What the messages of the refused members of a group read: the decider's system `graph`,
    /// the definition and expression of each node (`origin`), its runs and which nodes reach a
    /// meet or a difference (`wide`), with which nodes reach a refused node. Time linear in the
    /// system.
    fn new(
        members: usize,
        graph: Bes,
        origin: Vec<(usize, Arc<rec::Node>)>,
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
            Made::Meet(xs) => Made::Meet(map(xs)),
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
/// dropped (item GROUP-cycle-dup-names). Parts of two definitions are not merged, so each node's
/// origin, which the refusal message reads, is in the definition that wrote it; equal parts of
/// two definitions that neither reaches through unions keep their own nodes (follow-up
/// GROUP-cycle-dup-across).
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
                        rec::Shape::Tuple(xs) | rec::Shape::Atom(_, xs) | rec::Shape::And(xs) => {
                            todo.push(Step::Make(e, xs.len()));
                            todo.extend(xs.iter().rev().map(Step::Visit));
                            None
                        }
                        rec::Shape::Diff(a, _) => {
                            todo.push(Step::Make(e, 1));
                            todo.push(Step::Visit(a));
                            None
                        }
                        rec::Shape::Not(_) => {
                            unreachable!(
                                "admission keeps a recursive occurrence out of a complement"
                            )
                        }
                        rec::Shape::Param(_) | rec::Shape::Type(_) | rec::Shape::Ref(..) => {
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
                rec::Shape::And(_) => (Made::Meet(parts), true),
                rec::Shape::Diff(_, r) => (Made::Diff(r.class, parts[0]), true),
                rec::Shape::Morphism(l, u, _) => (Made::Mor(l.class, u.class, parts[0]), false),
                rec::Shape::Ref(..)
                | rec::Shape::Not(_)
                | rec::Shape::Param(_)
                | rec::Shape::Type(_) => {
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
        wider,
        leaves,
        same,
        union,
    }
}

mod names;
mod refused;

#[cfg(test)]
mod tests;
