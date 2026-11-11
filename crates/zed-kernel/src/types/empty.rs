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
use std::ops::{ControlFlow, Range};
use std::pin::Pin;
use std::sync::{Arc, Mutex};

use num_bigint::BigUint;

use super::bdd::{Bdd, Form, Part};
use super::bes::{Answer, Bes, Decision, Kind, decide};
use super::rec::unfold::eval;
use super::rec::{self, Env, Judgment, Why};
use super::{Held, Lits, Morphism, Node, Parts, Refusal, Row, Split, Type, Universes, Verdict};
use crate::frames::{Deep, Stack};
use crate::value::Value;
use shared::{ByType, ChainHint, ChainPlan, Digests, Literal2, TwoSat, list_step, only_atoms};

/// A set of types, hashed by their digests.
type TypeSet = HashSet<Type, Digests>;
/// The reads and blame a proof resting on a fork added for the type being decided, taken out
/// by [`Searching::take_fork`] and put back by [`Searching::restore_fork`].
type ForkSave = (Vec<usize>, Vec<(usize, Refusal)>);

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
    // Naive version (K62): a reader outside the group gets a search of its own that reads no
    // kept value, deciding again the part of the group it reaches, O(m·n) for m readers of a
    // group of n; used: the kept values read by index, O(1) per read.
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
    for m in members {
        let v = match m.judged() {
            Some(true) => Verdict::Empty,
            Some(false) if s.rep(m).is_some() => Verdict::Inhabited,
            // Complexity tradeoff: a member decided inhabited whose value the shared search does
            // not build gets a search of its own, which may read the whole group again; the X14
            // groups of 1024 and 2048 definitions measured for plan item VERDICT-group-share
            // needed none. Naive version (COMPLEXITY.md K56): a search of its own for every
            // member, n searches of a group of n, O(n²); used: one shared search of the group,
            // with this search of its own only for a member the shared one built no value of.
            Some(false) => m.verdict_alone(),
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
        GROUPS.with(|m| m.borrow_mut().clear());
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
        // `l01_23_subtyping::refusals::emptiness_counts_a_fork_as_inhabited_in_its_size`.
        // COMPLEXITY.md K35. A complete solution needs the subset construction over the forked
        // tuple types; deciding whether such a union holds every list is NFA universality,
        // PSPACE-complete. The answers of a search a fork ended may rest on it, so none is kept.
        // Used: the search stopped at the fork, polynomial in the types written (module
        // comment).
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
            let (mut rows, mut morphisms) = (HashSet::new(), HashSet::new());
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
                for a in p.atoms.names.values() {
                    visit(&a.payload, &mut seen, &mut stack);
                }
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

    /// The verdict of `self` by the front sweep ([`sweep::front_sweep`]), else by the
    /// prefix-chain sweep ([`Searching::sweep_verdict`]); `None` when `self` is outside both
    /// classes or both leave it to the search. For tests, which check it against an oracle of
    /// their own.
    pub fn sweep_verdict(&self) -> Option<Verdict> {
        sweep::front_sweep(self).or_else(|| self.chain_verdict())
    }

    /// Diagnostic counts of candidate and empty cell reads in the independent escape parse.
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
            ..Search::default()
        };
        // The front sweep left `self` to the search above.
        s.swept.insert(self.clone(), None);
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
            // L2) and a complete search, exponential in the types (the subset construction at
            // a fork, a split of the box in every component); used: the two searches already
            // run, each polynomial in the types written (module comment), and nothing more.
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
    /// For each type, the types it read, each with the search epoch when it was read.
    reads: Vec<Vec<(usize, usize)>>,
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
    blame: Option<Vec<(usize, Refusal, usize)>>,
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
    /// Nesting depth inside the general tuple/parts fallback for a list type outside
    /// [`Searching::prefix_chains`]; while non-zero, internal narrowed residual tail types go
    /// straight to the general decider without re-running `prefix_chains`.
    in_list_fallback: usize,
    /// The meet, difference or union of each pair of nodes the search built
    /// ([`Searching::cut`]), built once, by the nodes' local numbers ([`Type::node_id`]), which
    /// are never reused; the operands are kept with it. Read only by `entry`, never iterated.
    cuts: HashMap<(u64, u64, Cut), (Type, Type, Type), Digests>,
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
    // worst case, since the covering problem for residues is NP-hard. Used (COMPLEXITY.md
    // K34): O(residues tried × classes × primes²), polynomial in the periods, the length a
    // `BigUint` never walked.
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
        let rest = self.fork_resting();
        let fresh: Vec<usize> = (self.value_reads.iter().copied())
            .filter(|&v| self.answer[v] && !self.dead.contains(&v) && !rest[v])
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
        // A speculative value search keeps its uncertainty counter, but no permanent
        // refusal cause: the surrounding proof did not rely on that search.
        if self.open_forks && self.blame.is_some() {
            return;
        }
        let ep = self.epoch;
        match (&mut self.blame, self.current) {
            (Some(blame), Some(c)) if !self.open_forks => blame.push((c, r, ep)),
            _ if self.strict => {
                self.gave_up.get_or_insert(r);
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

    fn push_open_forks(&mut self) -> Option<(usize, usize, usize, bool)> {
        if self.deciding.is_empty() && self.open_forks_mark.is_none() {
            let mark = (
                self.types.len(),
                self.blame.as_ref().map_or(0, Vec::len),
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
        self.readers.truncate(mark);
        self.reads.truncate(mark);
    }

    /// For a search with `blame`, the cause each type's answer may rest on: a fork met in the
    /// decision of a type it read, directly or through others, else the first part counted as
    /// inhabited with nothing shown in such a decision. Each type is marked once, by walks over
    /// the readers from the types blamed, forks first and then the rest in the order met:
    /// O(types + reads + blame).
    fn causes(&self) -> Vec<Option<Refusal>> {
        let mut cause = vec![None; self.types.len()];
        let blame = self.blame.as_deref().unwrap_or_default();
        let forks = blame.iter().filter(|(_, r, _)| *r == Refusal::Fork);
        let rest = blame.iter().filter(|(_, r, _)| *r != Refusal::Fork);
        let mut stack = Vec::new();
        for &(t, r, _) in forks.chain(rest) {
            if cause[t].is_some() {
                continue;
            }
            cause[t] = Some(r);
            stack.push(t);
            while let Some(x) = stack.pop() {
                for &y in &self.readers[x] {
                    if (self.answer[x] || !self.answer[y]) && cause[y].is_none() {
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
                && self.add_reader(i, c)
            {
                let ep = self.epoch;
                self.reads[c].push((i, ep));
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
        self.readers.push(BTreeSet::new());
        if let Some(c) = self.current {
            let ep = self.epoch;
            self.reads[c].push((i, ep));
        }
        self.reads.push(Vec::new());
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
        let Some(blame) = self.blame.as_deref() else {
            return false;
        };
        let forked: BTreeSet<usize> = blame
            .iter()
            .filter_map(|&(x, r, _)| (r == Refusal::Fork).then_some(x))
            .collect();
        if forked.is_empty() {
            return false;
        }
        let mut stack: Vec<usize> = ts.into_iter().filter(|&t| self.answer[t]).collect();
        let mut seen: HashSet<usize> = stack.iter().copied().collect();
        while let Some(x) = stack.pop() {
            if forked.contains(&x) {
                return true;
            }
            for &(y, _) in &self.reads[x] {
                if self.answer[y] && seen.insert(y) {
                    stack.push(y);
                }
            }
        }
        false
    }

    /// For each type, whether its search or decision rests on a fork ([`Self::rests_on_fork`]):
    /// a type with answer `true` that reads, through types with answer `true`, a forked type
    /// with answer `true`. One walk back over the reads from the forked types, O(B + T + R).
    fn fork_resting(&self) -> Vec<bool> {
        let n = self.types.len();
        if self.refused == Some(Refusal::Fork) {
            return vec![true; n];
        }
        let mut rest = vec![false; n];
        let Some(blame) = self.blame.as_deref() else {
            return rest;
        };
        let mut stack: Vec<usize> = Vec::new();
        for &(x, r, _) in blame {
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
                for &(y, _) in reads {
                    read_by[y].push(x);
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
            for &(y, _) in &self.reads[x] {
                if self.deciding.contains(&y) || self.again.contains(&y) || self.round.contains(&y)
                {
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
// instead, the chains cost `r6twowide` and `r6threeun` 45-65% more than main. Given up: a list
// whose items are lists of the same atom names (a list of lists) leaves its items to the search.
///
/// Also the atom types among them that are not lists (`Search::wraps`): each payload of a
/// literal union of tuple rows with no link of a list in it.
fn fields(roots: &[Type]) -> (Vec<Type>, Vec<Type>) {
    let (mut seen, mut out, mut wraps) = (HashSet::new(), Vec::new(), Vec::new());
    let mut stack: Vec<Type> = roots.iter().rev().cloned().collect();
    while let Some(t) = stack.pop() {
        if !seen.insert(t.node_addr()) {
            continue;
        }
        out.push(t.clone());
        let Node::Parts(p, _) = &*t.0 else {
            continue;
        };
        // An atom's payload components, but not one with an atom of the same name: that is a
        // link of a list through the atom (a cons cell's tail), whose walk would make every tail
        // of the list a root.
        // Only the names whose payload lists something (`Atoms::payloads`): reading every name
        // here cost O(names) per type, n^2 on a chain of n failure atoms (l01_27_absences), and
        // a name whose payload lists nothing adds no component and leaves `wrap` as it is.
        let mut wrap = !p.atoms.names.is_empty();
        for name in &p.atoms.payloads {
            let Some(a) = p.atoms.names.get(name) else {
                continue;
            };
            if a.bare {
                continue;
            }
            let pp = a.payload.p();
            wrap &= !pp.tuples.rest && !pp.structs;
            for b in pp.tuples.lens.values() {
                let Some(rows) = b.union_rows() else {
                    wrap = false;
                    continue;
                };
                for row in rows {
                    for c in row.iter() {
                        if c.p().atoms.names.contains_key(name) {
                            wrap = false;
                        } else {
                            stack.push(c.clone());
                        }
                    }
                }
            }
        }
        if wrap {
            wraps.push(t.clone());
        }
        for b in p.tuples.lens.values() {
            for row in b.union_rows().unwrap_or_default() {
                stack.extend(row.iter().cloned());
            }
        }
        for m in p.morphisms.union_rows().unwrap_or_default() {
            stack.push(m.value.clone());
        }
    }
    (out, wraps)
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
        let (written, wraps) = fields(roots);
        {
            let mut s = self.s();
            s.roots.extend(written.into_iter().map(|r| (r, ())));
            s.wraps.extend(wraps.into_iter().map(|r| (r, ())));
        }
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
            let mut guard = self.s();
            let s = &mut *guard;
            if let Some(blame) = &mut s.blame {
                blame.retain(|&(x, _, _)| x != t);
            }
            for (u, _) in std::mem::take(&mut s.reads[t]) {
                s.readers[u].remove(&t);
            }
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
            None => {
                if let Some(r) = self.swept(&ty) {
                    if r.is_some() {
                        self.s().witnessed.insert(t);
                    }
                    r.is_none()
                } else if self.s().in_list_fallback > 0 {
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
                                let is_atom_list = !ty.p().atoms.names.is_empty()
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
                            let is_atom_list =
                                !ty.p().atoms.names.is_empty() && !self.s().wraps.contains_key(&ty);
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
                let ep = s.epoch;
                match (&mut s.blame, s.current) {
                    (Some(blame), Some(c)) => blame.push((c, Refusal::Fork, ep)),
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
            let from: Vec<usize> = read.iter().map(|&(u, _)| u).chain(sub).collect();
            !from.is_empty() && s.rests_on_fork(from)
        };
        if !on_fork {
            return None;
        }
        let saved_reads = if let Some(c) = c {
            let start = s.reads[c].partition_point(|&(_, e)| e < ep);
            let dropped: Vec<usize> = s.reads[c].drain(start..).map(|(u, _)| u).collect();
            // Complexity tradeoff (COMPLEXITY.md K102): the naive test scans the reads kept for
            // each read dropped, O(D K); a set of the kept reads makes it O(D + K) expected.
            let kept: HashSet<usize> = if dropped.is_empty() {
                HashSet::new()
            } else {
                s.reads[c].iter().map(|&(v, _)| v).collect()
            };
            for &u in &dropped {
                if !kept.contains(&u) {
                    s.readers[u].remove(&c);
                }
            }
            dropped
        } else {
            Vec::new()
        };
        let saved_blame = if let Some(b) = &mut s.blame {
            let start = b.partition_point(|&(_, _, e)| e < ep);
            let mut saved = Vec::new();
            let mut k = start;
            for idx in start..b.len() {
                if Some(b[idx].0) == c {
                    saved.push((b[idx].0, b[idx].1));
                } else {
                    b[k] = b[idx];
                    k += 1;
                }
            }
            b.truncate(k);
            saved
        } else {
            Vec::new()
        };
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
            for u in reads {
                s.add_reader(u, c);
                s.reads[c].push((u, ep));
            }
        }
        if let Some(b) = &mut s.blame {
            b.extend(blame.into_iter().map(|(x, r)| (x, r, ep)));
        }
    }

    /// Whether one of `ts` is empty, tried in order up to the first that is without a fork, or
    /// the first that is with one.
    async fn any_empty(&'m self, ts: &[Type]) -> bool {
        let mut first_fork = None;
        for t in ts {
            match self.empty_fork(t).await {
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
        let mut forks = Vec::new();
        for a in p.atoms.names.values() {
            if a.bare {
                return false;
            }
            match self.empty_fork(&a.payload).await {
                (false, _) => return false,
                (true, Some(fork)) => forks.push(fork),
                (true, None) => {}
            }
        }
        if p.structs || p.tuples.rest {
            return false;
        }
        for (len, b) in &p.tuples.lens {
            let snap = self.fork_snapshot();
            let empty = match b.union_rows() {
                // A union of rows is empty when each row has an empty column, and only then.
                Some(rows) => {
                    let mut all = true;
                    let mut row_forks = Vec::new();
                    for a in &rows {
                        let row_snap = self.fork_snapshot();
                        if !self.any_empty(a).await {
                            all = false;
                            break;
                        }
                        if let Some(fork) = self.take_fork(row_snap, None) {
                            row_forks.push(fork);
                        }
                    }
                    if all {
                        for fork in row_forks {
                            self.restore_fork(fork);
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
            if let Some(fork) = self.take_fork(snap, None) {
                forks.push(fork);
            }
        }
        let snap = self.fork_snapshot();
        let morphisms_empty = match p.morphisms.union_rows() {
            // A union of morphism types is empty when each of them admits nothing.
            Some(rows) => {
                let mut all = true;
                let mut row_forks = Vec::new();
                for a in &rows {
                    let row_snap = self.fork_snapshot();
                    if !self.no_morphism(a).await {
                        all = false;
                        break;
                    }
                    if let Some(fork) = self.take_fork(row_snap, None) {
                        row_forks.push(fork);
                    }
                }
                if all {
                    for fork in row_forks {
                        self.restore_fork(fork);
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
            cells: (0..n).map(|_| Vec::new()).collect(),
            cell_of: vec![0; atoms.len() * n],
            opens: vec![0; n],
            changed: vec![true; n],
            missed: vec![0; atoms.len()],
            loose: vec![(0, 0); atoms.len()],
            index: BTreeMap::new(),
            atoms: Vec::new(),
            log: Vec::new(),
            forked_holds: Vec::new(),
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
        self.retest(&mut g).await;
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
            let mut forked = Vec::new();
            for &j in &changed {
                for c in 0..g.cells[j].len() {
                    let cell = &g.cells[j][c];
                    if !cell.open || !cell.rows.iter().any(|&k| g.missed[k] == 0) {
                        continue;
                    }
                    if missed {
                        if let Some(b) = g.r[j].scalar_cell(&cell.ty, true) {
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
                        if let Some(b) = g.r[j].scalar_cell(&cell.ty, false) {
                            if b {
                                g.close(j, c, false);
                            }
                            continue;
                        }
                        let t = self.cut(&g.r[j], &cell.ty, Cut::Minus);
                        match self.empty_fork(&t).await {
                            (true, None) => g.close(j, c, false),
                            (true, Some(fork)) => g.forked_holds.push((j, c, fork)),
                            (false, _) => {}
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

    /// Notes a fork met in the decision of a verdict: against the type being decided in a search
    /// with several roots, else as the refusal that ends the search.
    fn refuse_fork(&self) {
        let mut guard = self.s();
        let s = &mut *guard;
        let ep = s.epoch;
        match (&mut s.blame, s.current) {
            (Some(blame), Some(c)) => blame.push((c, Refusal::Fork, ep)),
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
                for a in &rows {
                    let snap = self.fork_snapshot();
                    if !self.any_empty(a).await {
                        all = false;
                        break;
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
            if let Some((j, classes)) = classes(g, &open) {
                let mut each = Each::Decide { may_cover };
                return self.split_classes(g, &f, j, &classes, &mut each).await;
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
                // (`Search::causes`). Used: the refusal, so the search stays polynomial in the
                // types written (module comment).
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
                    continue;
                }
                let mut all: Vec<(Type, Vec<usize>)> = pieces.into_iter().collect();
                let rest = &g.r[j] - &union;
                if self.empty_fork(&rest).await != (true, None) {
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
                // below (`l01_23_subtyping::refusals::a_union_of_pairs_less_pairs_holding_them_is_empty_in_its_size`,
                // COMPLEXITY.md K80).
                if let Some(parts) = f.disjoint_disjuncts() {
                    let mut forks = Vec::new();
                    for d in parts {
                        let snap = self.fork_snapshot();
                        if !self.piece(g.r.clone(), d, true).await {
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
                let mut forks = Vec::new();
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
            let mut narrowed = false;
            let mut forked_cut = None;
            for j in 0..g.r.len() {
                let mut tried = BTreeSet::new();
                // A cell closed on the component misses or holds it, so its pieces are the
                // component and nothing, and narrow nothing.
                for cell in g.open_cells(j, &open) {
                    if !g.cells[j][cell].open {
                        continue;
                    }
                    let a = g.cells[j][cell].ty.clone();
                    for (c, missed) in [(&a & &g.r[j], false), (&g.r[j] - &a, true)] {
                        if tried.contains(&c)
                            || self.empty_fork(&c).await.0
                            || self.empty_fork(&(&g.r[j] - &c)).await.0
                        {
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
                                    narrowed = true;
                                    break;
                                }
                                Some(fork) => {
                                    forked_cut.get_or_insert((j, c, cell, missed, fork));
                                }
                            }
                        }
                    }
                }
            }
            if !narrowed && let Some((j, c, cell, missed, fork)) = forked_cut {
                self.restore_fork(fork);
                let t = &g.r[j] - &c;
                g.shrink(j, t);
                g.close(j, cell, !missed);
                narrowed = true;
            }
            if narrowed {
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
        let mut forks = Vec::new();
        let out = f.restrict(&|a| at(a).map(|_| false));
        if out.is_leaf() != Some(false) {
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
            let (lo, hi) = (this.start..m, m..this.end);
            halves.push((f.clone(), hi.clone(), Some(lo.clone())));
            halves.push((f, lo, Some(hi)));
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
                s.reads[c].push((i, ep));
            }
        }
        dead
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
                (true, true) if bare.is_none() => bare = Some(name.clone()),
                (false, true) => {}
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
        let atoms = f.distinct_atoms();
        if taken.len() + refused.len() != atoms.len() || atoms.is_empty() {
            return None;
        }
        let taken_set: BTreeSet<&Row> = taken.iter().collect();
        if !f.eval(&|a| taken_set.contains(a)) {
            return None;
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
            && !p.strings.cofinite
            && p.strings.values.is_empty()
            && !p.structs
            && p.morphisms.is_leaf() == Some(false)
            && !p.atoms.cofinite
            && p.atoms.names.is_empty()
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
        if self.s().in_list_fallback > 0
            || t.p().atoms.names.is_empty()
            || !self.s().roots.contains_key(t)
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
        s.members.insert((r, t.clone()), Some(true));
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
            || p.strings.cofinite
            || !p.strings.values.is_empty()
            || p.structs
            || p.morphisms.is_leaf() != Some(false)
            || !p.tuples.is_default()
            || p.atoms.cofinite
        {
            return None;
        }
        let mut link: Option<(std::sync::Arc<str>, Type)> = None;
        for (name, a) in &p.atoms.names {
            match (a.bare, a.payload == Type::empty()) {
                (true, _) => return None,
                (false, true) => {}
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
                        Some(prev) if prev == &c => {
                            if !carriers.contains(&a[1]) {
                                carriers.push(a[1].clone());
                            }
                        }
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
                                    Some(prev) if prev == &c => {
                                        if !carriers.contains(&cur) {
                                            carriers.push(cur);
                                        }
                                    }
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
                || xp.strings.cofinite
                || !xp.strings.values.is_empty()
                || xp.structs
                || xp.morphisms.is_leaf() != Some(false)
                || !xp.tuples.is_default()
                || xp.atoms.cofinite
            {
                return None;
            }
            let mut has_stop = false;
            let mut l_payload: Option<Type> = None;
            for (n, a) in &xp.atoms.names {
                match (a.bare, a.payload == Type::empty()) {
                    (true, true) if *n == stop_name => has_stop = true,
                    (false, true) => {}
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
        let mut node_of: ByType<Option<usize>> = ByType::with_hasher(Digests::new());
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
                        .names
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
        let mut neg_rows_by_head: ByType<Vec<usize>> = ByType::with_hasher(Digests::new());
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
        let mut pos_group_of: [ByType<usize>; 2] = [
            ByType::with_hasher(Digests::new()),
            ByType::with_hasher(Digests::new()),
        ];
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
        let mut head_reps: ByType<usize> = ByType::with_hasher(Digests::new());
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
        s.members.insert((cur, t.clone()), Some(true));
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
            return p.atoms.names.get(stop).map_or(p.atoms.cofinite, |a| a.bare);
        }
        let p = t.p();
        let Some(a) = p.atoms.names.get(link) else {
            return p.atoms.cofinite;
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
                            .names
                            .get(stop)
                            .map_or(rp.atoms.cofinite, |x| x.bare);
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
        let mut head_ids: ByType<usize> = ByType::with_hasher(Digests::new());
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
                || xp.strings.cofinite
                || !xp.strings.values.is_empty()
                || xp.structs
                || xp.morphisms.is_leaf() != Some(false)
                || !xp.tuples.is_default()
                || xp.atoms.cofinite
            {
                return None;
            }
            let mut has_stop = false;
            let mut l_payload: Option<Type> = None;
            for (n, at) in &xp.atoms.names {
                match (at.bare, at.payload == Type::empty()) {
                    (true, true) if n == stop => has_stop = true,
                    (false, true) => {}
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
        let mut node_of: ByType<Option<usize>> = ByType::with_hasher(Digests::new());
        let mut canon_verify: HashMap<(bool, usize, Option<(usize, usize)>, usize), usize> =
            HashMap::new();

        let mut unfold = |start: &Type,
                          intern_head: &mut dyn FnMut(&Type) -> usize|
         -> Option<usize> {
            if let Some(&res) = node_of.get(start) {
                return res;
            }
            let mut path: Vec<(Type, bool, usize, Option<(usize, usize)>)> = Vec::new();
            let mut seen_on_path: ByType<usize> = ByType::with_hasher(Digests::new());
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
            for b in 0..17 {
                if (k >> b) & 1 != 0 {
                    u = nodes[u].up[b];
                }
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
        // A root list in the front sweep's class: its checked value, or none when it is empty.
        if let Some(r) = self.swept(t) {
            return r;
        }
        // A list of a carrier cycle less prefix chains: a witness list from the sweep,
        // verified independently by `check_chain_witness` before being returned.
        if self.s().in_list_fallback == 0
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
        let list_fallback =
            matches!(self.s().chains.get(t), Some(None)) && !self.s().wraps.contains_key(t);
        for (name, a) in &p.atoms.names {
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
                let permitted = m.guarantee == m.permission
                    || m.guarantee == Type::empty()
                    || m.permission == Type::top();
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
                // `l01_23_subtyping::refusals::a_union_of_lists_by_the_place_of_a_one_is_refused_in_its_size`
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
                if self.s().kept_forks > forks || open_fork {
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
    /// it or none. Its searches neither end at a fork nor follow one: a forked piece counts as
    /// inhabited with nothing shown.
    async fn refine(&'m self, start: Vec<Type>, f: &Part<Row>) -> Option<Vec<Type>> {
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
        // `l01_23_subtyping::refusals::refining_a_box_follows_no_fork_in_its_size`.
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
    /// so another morphism type stands as unknown (`eval3`), settling `f` whenever `m` alone
    /// determines its value (as in `m | n` or `!m`).
    fn closure_member(m: &Morphism, f: &Part<Morphism>) -> Option<bool> {
        f.eval3(&|a| (a == m).then_some(true))
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
                let mut forked_atoms = Vec::new();
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
                            let _ = self.take_fork(snap, None);
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
                                let _ = self.take_fork(snap, None);
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
                    let mut forks = Vec::new();
                    for a in f.distinct_atoms().iter() {
                        let piece = f.restrict(&|b| (b == a).then_some(true));
                        if piece.is_leaf() == Some(true) {
                            return false;
                        }
                        let snap = self.fork_snapshot();
                        if !self.morphisms(self.meet(&r, a), piece, false).await {
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
fn classes(g: &Region, open: &[usize]) -> Option<(usize, Vec<Class>)> {
    (0..g.r.len()).find_map(|j| {
        if g.opens[j] < open.len() || open.iter().any(|&k| !g.is_open(k, j)) {
            return None;
        }
        let cells: Vec<usize> = g.open_cells(j, open).into_iter().collect();
        let groups = overlaps(cells.iter().map(|&c| &g.cells[j][c].ty));
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
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Key {
    Bool(u8),
    Lit(usize, Value),
    Atom(std::sync::Arc<str>),
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
fn listed(p: &Parts, u: usize, none: &Type) -> (bool, Vec<(Key, bool)>) {
    match u {
        0..4 => {
            let l = [&p.ints, &p.rats, &p.floats, &p.strings][u];
            let ks = l
                .values
                .iter()
                .map(|v| (Key::Lit(u, v.clone()), !l.cofinite));
            (l.cofinite, ks.collect())
        }
        4 => {
            let ks = p.atoms.names.iter();
            let ks = ks.map(|(n, a)| (Key::Atom(n.clone()), a.bare || a.payload != *none));
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
fn local<'a>(p: &'a Parts, none: &Type) -> Local<'a> {
    let mut points: Vec<Key> = (0..2u8)
        .filter(|b| p.bools >> b & 1 == 1)
        .map(Key::Bool)
        .collect();
    if p.structs {
        points.push(Key::All(6));
    }
    if p.morphisms.is_leaf() != Some(false) {
        points.push(Key::All(7));
    }
    let mut kids = Vec::new();
    for (n, a) in &p.atoms.names {
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
                inside.push(&row[0]);
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
    let mut lists = Vec::with_capacity(6);
    for u in 0..6 {
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
/// the types inside a type are its payloads and the first components of its tuples (each type
/// reaches every member): one node per class of nodes, as one walk over the members merges
/// them, the members' types met again at another node. The types of groups below this one are
/// leaves, each at its node. It is the same trie from every member, a member's node being its
/// class. What a type lists at a class is cut to what `overlaps` reads of it: the keys that
/// every cofinite list there lists, or, with no cofinite list, the keys held there.
struct Group {
    /// The group's number, from one count per thread.
    id: usize,
    nodes: Vec<GroupNode>,
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
    fn set_deep(nodes: &mut [GroupNode]) {
        let mut parents: Vec<Vec<usize>> = vec![Vec::new(); nodes.len()];
        for (x, n) in nodes.iter().enumerate() {
            for &(_, c) in &n.kids {
                parents[c].push(x);
            }
        }
        let lower = |t: &Type| {
            let g = GROUPS.with(|m| m.borrow().get(t).cloned());
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

thread_local! {
    /// The group of each type that `overlaps` met inside a type, and the type's node there,
    /// until `Type::forget_emptiness`.
    // Complexity tradeoff: every type met inside the cells of the unit's splits is kept with
    // its group until the unit ends, O(their total size) of memory; it buys each group's trie
    // made once, where made for each cell a ring of k types costs k per cell and order k^2 in
    // all (COMPLEXITY.md K36). Trigger: any split into classes.
    static GROUPS: RefCell<ByType<(std::rc::Rc<Group>, usize)>> =
        const { RefCell::new(ByType::with_hasher(Digests::new())) };
    /// The number of the next [`Group`] made on this thread.
    static GROUP_IDS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The state of the walk of [`group_of`]: per type met, by its number in the order met, the
/// type, its parts read, its group's number once its walk ends (`usize::MAX` before), and the
/// lowest number it reaches through types whose groups are not made; the types met whose
/// groups are not made, in order; and the walk, each type with its next type inside, by edge
/// and by place under the edge.
struct Walked<'a> {
    number: HashMap<&'a Type, usize>,
    types: Vec<&'a Type>,
    locals: Vec<Local<'a>>,
    group: Vec<usize>,
    low: Vec<usize>,
    open: Vec<usize>,
    walk: Vec<(usize, usize, usize)>,
}

impl<'a> Walked<'a> {
    fn visit(&mut self, t: &'a Type, held: &'a Held, none: &Type) {
        let v = self.types.len();
        self.number.insert(t, v);
        self.types.push(t);
        self.locals.push(local(t.p_held(held), none));
        self.group.push(usize::MAX);
        self.low.push(v);
        self.open.push(v);
        self.walk.push((v, 0, 0));
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
                        Entry::Occupied(o) => trie.merge(*o.get(), y),
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
        for t in below {
            nodes[at(node[t])].below.push(t.clone());
        }
        Group::set_deep(&mut nodes);
        let id = GROUP_IDS.with(|n| n.replace(n.get() + 1));
        let group = std::rc::Rc::new(Group { id, nodes });
        GROUPS.with(|m| {
            let mut m = m.borrow_mut();
            for &v in members {
                let t = self.types[v];
                m.insert(t.clone(), (group.clone(), at(node[t])));
            }
        });
    }
}

/// The group of `t` and its node there ([`Group`]), made with each group below it not yet
/// made, by Tarjan's walk over the types inside, which reads each type's parts once: a group
/// is made when its walk ends, after the groups below it.
fn group_of(t: &Type) -> (std::rc::Rc<Group>, usize) {
    if let Some(g) = GROUPS.with(|m| m.borrow().get(t).cloned()) {
        return g;
    }
    let none = Type::empty();
    let held = Held::default();
    let mut w = Walked {
        number: HashMap::new(),
        types: Vec::new(),
        locals: Vec::new(),
        group: Vec::new(),
        low: Vec::new(),
        open: Vec::new(),
        walk: Vec::new(),
    };
    w.visit(t, &held, &none);
    let mut groups = 0;
    while let Some(&(v, k, j)) = w.walk.last() {
        let top = w.walk.len() - 1;
        let kids = &w.locals[v].kids;
        if k < kids.len() {
            if j == kids[k].inside.len() {
                w.walk[top] = (v, k + 1, 0);
                continue;
            }
            let x = kids[k].inside[j];
            w.walk[top] = (v, k, j + 1);
            match w.number.get(x) {
                Some(&x) => {
                    if w.group[x] == usize::MAX {
                        w.low[v] = w.low[v].min(x);
                    }
                }
                None => {
                    if !GROUPS.with(|m| m.borrow().contains_key(x)) {
                        w.visit(x, &held, &none);
                    }
                }
            }
            continue;
        }
        w.walk.pop();
        if let Some(&(u, _, _)) = w.walk.last() {
            w.low[u] = w.low[u].min(w.low[v]);
        }
        if w.low[v] == v {
            let mut members = Vec::new();
            while let Some(m) = w.open.pop() {
                w.group[m] = groups;
                members.push(m);
                if m == v {
                    break;
                }
            }
            w.make(&members, groups);
            groups += 1;
        }
    }
    GROUPS
        .with(|m| m.borrow().get(t).cloned())
        .expect("the group of `t` is made")
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
                    work.push(Work::Bind(kid, p, *r));
                }
                (None, None) => {
                    let v = trie.add();
                    pending.push(Some((p, *r)));
                    trie.kids[x].insert(e.clone(), v);
                    at[p].insert(*r, v);
                }
            }
        }
        work.extend(n.below.iter().map(|t| Work::Place(x, t.clone(), i)));
    }
}

/// The types `ts` in classes, by index in order of their first members, joined when they share
/// a key: two types of different classes are disjoint. The keys sit in a trie: the atoms of
/// one name are keyed by their payload's keys under the node of the name, and the tuples of one
/// length by the keys of their first component under the node of the length, so `#a((1,))` and
/// `#a((2,))`, or `(1,)` and `(2,)`, share no key. A type that holds every value under a node,
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
// one large group. Tests: `types::empty::tests::types_that_each_reach_a_ring_of_names_scale`
// (the ring of names, the same under a one-tuple, and beside a whole under each name),
// `types_that_each_reach_a_ring_holding_lower_types_scale` (each member holding `#b_j((int,))`,
// `#b((int,))` under one name, or `#c_j((L,))` for a recursive list type `L`),
// `types_that_meet_are_joined_in_random_groups_holding_lower_types` (400 random cases against
// the meets), `types_that_each_reach_a_ring_of_names_are_apart`,
// `classes_inside_a_recursive_group_follow_its_merged_nodes`, and
// `l01_23_subtyping::group_oracle::verdicts_of_a_ring_of_the_group_that_hung_the_search_scale`.
// COMPLEXITY.md K36.
fn overlaps<'a>(ts: impl Iterator<Item = &'a Type>) -> Vec<Vec<usize>> {
    let none = Type::empty();
    let held = Held::default();
    let mut trie = Trie::new();
    let mut s = Placing::default();
    s.sync(&trie);
    let mut parent: Vec<usize> = Vec::new();
    // The groups placed for each cell, by cell and group number, with their placements. A
    // type of a group placed for the cell is placed: met again, its node and the new one are
    // merged.
    let mut placed: HashMap<(usize, usize), usize> = HashMap::new();
    let mut work: Vec<Work> = Vec::new();
    for (i, t) in ts.enumerate() {
        parent.push(i);
        let l = local(t.p_held(&held), &none);
        s.points.extend(l.points.into_iter().map(|k| (0, k, i)));
        s.lists.extend(l.lists.into_iter().map(|li| (0, li, i)));
        for kid in l.kids {
            let y = trie.child(0, kid.edge);
            s.sync(&trie);
            s.reach(&mut trie, y, &mut work);
            if kid.bare {
                s.points.push((y, Key::Bare, i));
            }
            if kid.whole {
                s.wholes.push((y, i));
            }
            work.extend(kid.inside.into_iter().map(|t| Work::Place(y, t.clone(), i)));
        }
        while let Some(w) = work.pop() {
            match w {
                Work::Place(y, t, i) => {
                    let (g, c) = group_of(&t);
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
                            work.push(Work::Bind(y, p, c));
                        }
                    }
                }
                Work::Bind(y, p, q) => {
                    let y = trie.find(y);
                    s.reach(&mut trie, y, &mut work);
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
    let mut groups: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for i in 0..parent.len() {
        let r = root(&mut parent, i);
        groups.entry(r).or_default().push(i);
    }
    groups.into_values().collect()
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
    // verdict refuses as `Refusal::Fork` after a search for a value
    // (`the_product_of_k_parity_lists_is_refused_by_its_fork`: 178M, 1.11G and 4.51G
    // instructions at k 2, 3 and 4). COMPLEXITY.md K84. Naive version: a recursive occurrence
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
                rec::Shape::And(_) => {
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

mod escape;
mod names;
mod refused;
mod shared;
mod sweep;

#[cfg(test)]
mod tests;
