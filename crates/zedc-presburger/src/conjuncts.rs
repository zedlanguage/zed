//! The linear relation of a scope (step L1.39) as a persistent set of conjuncts, with the
//! conjuncts that mention each name, of the constraints on each term the tighter one, and of
//! the disjunctions of two constraints on each pair of terms those that no other implies.
//!
//! A scope is copied for each case of a test and the cases are joined, so the relation is held
//! in persistent maps: a copy costs O(1), a new conjunct O(log n) in the size of the relation,
//! and two relations made from one by a few changes are compared, and their differing
//! conjuncts found, in time near the number of changes. The conjuncts are in the order of
//! formulas, so a relation does not depend on the order its conjuncts were added in.
//!
//! Published work used in this file. Each site names the author; the full citation is in the
//! crate's `lib.rs`, "References". Karr 1976, doi:10.1007/bf00268497 (the join is in
//! `hull.rs`); Shostak 1981, doi:10.1145/322276.322288; Tarjan 1975, doi:10.1145/321879.321884
//! (union by rank and path compression); Blelloch, Ferizovic and Sun 2016,
//! doi:10.1145/2935764.2935768, and Brown and Tarjan 1979, doi:10.1145/322123.322127 (union of
//! ordered sets, as `vendor/imbl` runs it); Holm, de Lichtenberg and Thorup 2001,
//! doi:10.1145/502090.502095.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;
use std::ops::{Bound, RangeBounds};
use std::sync::Arc;

use imbl::shared_ptr::DefaultSharedPtr;
use imbl::{GenericHashMap, OrdMap, OrdSet};
use zed_kernel::digest::{Digest, TextState};

use super::presburger::{Atom, Con, Factor, Formula, Id, Lin, Model, Rel, Shared};
use zedc_int::int::Int;

/// The values of a set kept for each name, in a persistent map.
#[derive(Clone, PartialEq, Debug)]
pub struct Uses<T: Ord + Clone>(OrdMap<Arc<str>, OrdSet<T>>);

impl<T: Ord + Clone> Default for Uses<T> {
    fn default() -> Self {
        Uses(OrdMap::new())
    }
}

impl<T: Ord + Clone> Uses<T> {
    /// Records that `name` is used by `t`.
    // Complexity tradeoff: naive version, `entry(name).or_default()`, which in imbl looks the
    // name up once to choose the entry and again to give the set: two descents of O(log n)
    // name comparisons each when the name is there, as it is for all but its first value.
    // Used: one descent that gives the set, and a second only to insert a new name. The same
    // O(log n), half the comparisons. COMPLEXITY.md row ST-chain-raise-reverse-log.
    pub fn add(&mut self, name: &Arc<str>, t: &T) {
        match self.0.get_mut(name) {
            Some(s) => {
                s.insert(t.clone());
            }
            None => {
                self.0.insert(name.clone(), OrdSet::unit(t.clone()));
            }
        }
    }

    /// Forgets that `name` is used by `t`.
    pub fn remove(&mut self, name: &Arc<str>, t: &T) {
        if let Some(s) = self.0.get_mut(name) {
            s.remove(t);
            if s.is_empty() {
                self.0.remove(name);
            }
        }
    }

    /// The values that use `name`.
    pub fn of(&self, name: &str) -> impl Iterator<Item = &T> {
        self.0.get(name).into_iter().flatten()
    }

    /// The number of values that use `name`, in O(log n).
    pub fn count(&self, name: &str) -> usize {
        self.0.get(name).map_or(0, OrdSet::len)
    }

    /// Whether `t` uses `name`.
    pub fn has(&self, name: &str, t: &T) -> bool {
        self.0.get(name).is_some_and(|s| s.contains(t))
    }

    /// The names that are used.
    pub fn names(&self) -> impl Iterator<Item = &Arc<str>> {
        self.0.keys()
    }

    /// The persistent set of the values that use `name`, which a copy kept for later shares,
    /// so that the two are compared in the values that differ.
    pub fn set(&self, name: &str) -> Option<&OrdSet<T>> {
        self.0.get(name)
    }

    /// [`Uses::add`], through the last change `last` made ([`Last`]).
    pub fn add_with(&mut self, name: &Arc<str>, t: &T, last: &mut Last<T>) {
        self.change(name, t, true, last);
    }

    /// [`Uses::remove`], through the last change `last` made ([`Last`]).
    pub fn remove_with(&mut self, name: &Arc<str>, t: &T, last: &mut Last<T>) {
        self.change(name, t, false, last);
    }

    /// Adds (`add`) or removes `t` at `name`: when `last` made the same change to a set equal
    /// by pointer to the one at `name`, its result is taken in O(1); otherwise the change is
    /// made and kept in `last`.
    fn change(&mut self, name: &Arc<str>, t: &T, add: bool, last: &mut Last<T>) {
        let now = self.0.get(name);
        if let Some((v, a, before, after)) = &last.0
            && *a == add
            && v == t
            && match (before, now) {
                (Some(x), Some(y)) => x.ptr_eq(y),
                (None, None) => true,
                _ => false,
            }
        {
            match after {
                Some(s) => {
                    self.0.insert(name.clone(), s.clone());
                }
                None => {
                    self.0.remove(name);
                }
            }
            return;
        }
        let before = now.cloned();
        if add {
            self.add(name, t);
        } else {
            self.remove(name, t);
        }
        last.0 = Some((t.clone(), add, before, self.0.get(name).cloned()));
    }
}

/// The last change made through [`Uses::add_with`] or [`Uses::remove_with`]: the value,
/// whether it was added, and the set at the name before and after (`None` for no set), so that
/// the same change to a set equal by pointer to the one before takes the one after in O(1).
/// The result is the same set: a persistent set is not changed once shared, so sets equal by
/// pointer hold the same values, and the change depends on the values and `t` alone.
// Complexity tradeoff: naive version, each index of a conjunct's names (`users`, `moving` and
// `free` of [`Conjuncts`], `syms` and `forest` of [`Blocks`]) inserted the conjunct into its own
// set at each name, O(log d) comparisons of formulas and a path copy of O(log d) nodes for a
// name of d conjuncts, though the sets of one name are often one persistent set (a name none of
// whose conjuncts is in a star or bounds it alone has the same set in all five), and two names
// that every conjunct mentions both of have one set too. Used: the last change is kept, and a
// set equal by `ptr_eq` to its set before takes its set after: O(log d) for the first set
// changed, O(1) for each set shared with it after, and the map's own O(log n) descent at the
// name for each, so the indexes go on sharing their sets. Tradeoffs: a set that matches no kept
// change costs as before, the set before kept alive by `last` can make a set held nowhere else
// copied along its path rather than changed in place (the same O(log d)), and an index that is
// changed between two others (`eq_users`) goes through plain `add` so as not to replace the kept
// change. Trigger of the old cost: stair_holes_mix, whose k disjunctions all mention `x` and
// `y`, inserted each into eight sets of k conjuncts, 1,518M of 15,107M instructions at k =
// 16,384 and 142M of 1,688M at 2,048 (callgrind). Test
// `l01_39_scope_relations::families::bench::stair_holes_mix_scales`; COMPLEXITY.md row
// PERF-l139-shared-uses.
#[derive(Clone, Debug)]
pub struct Last<T: Ord + Clone>(Option<Change<T>>);

/// One change [`Last`] keeps: the value, whether it was added, and the set before and after.
type Change<T> = (T, bool, Option<OrdSet<T>>, Option<OrdSet<T>>);

impl<T: Ord + Clone> Default for Last<T> {
    fn default() -> Self {
        Last(None)
    }
}

impl<T: Ord + Clone + Default> Uses<(usize, T)> {
    /// The values kept at `name` with a count in `counts`, in O(log n) and their number.
    fn within(&self, name: &str, counts: impl RangeBounds<usize>) -> Vec<T> {
        let Some(s) = self.0.get(name) else {
            return Vec::new();
        };
        // The least value, the empty name or hub set, so that `(c, least)` comes before every
        // entry of count `c`.
        let least = T::default();
        let lo = match counts.start_bound() {
            Bound::Included(&c) => Bound::Included((c, least.clone())),
            Bound::Excluded(&c) => Bound::Included((c + 1, least.clone())),
            Bound::Unbounded => Bound::Unbounded,
        };
        let hi = match counts.end_bound() {
            Bound::Included(&c) => Bound::Excluded((c + 1, least)),
            Bound::Excluded(&c) => Bound::Excluded((c, least)),
            Bound::Unbounded => Bound::Unbounded,
        };
        s.range((lo, hi)).map(|(_, n)| n.clone()).collect()
    }
}

/// The constraints kept by the rule that keeps the tighter of two, of one relation, by their
/// term ([`Conjuncts::tight`]).
type Tight = OrdMap<Arc<BTreeMap<Atom, Int>>, Arc<Formula>>;

/// The index of the map of `rel`'s constraints in [`Conjuncts::tight`].
fn tight_at(rel: Rel) -> usize {
    match rel {
        Rel::Ge => 0,
        Rel::Eq => 1,
    }
}

/// Conjuncts removed from every index but the blocks, by their atoms ([`Conjuncts::swap`]).
type Held = BTreeMap<BTreeSet<Atom>, Vec<Arc<Formula>>>;

/// The key of a disjunction of two constraints `f + c >= 0 || g + d >= 0` for the rule that
/// keeps the stronger of two ([`Conjuncts::pair`]): its two terms `f` and `g`, in order.
type PairKey = (BTreeMap<Atom, Int>, BTreeMap<Atom, Int>);

/// The disjunctions kept on one [`PairKey`], each by its constant on the first term with its
/// constant on the second: none implies another, so as the first constant rises the second
/// falls.
type Front = OrdMap<Int, (Int, Arc<Formula>)>;

/// `g` as a disjunction of two constraints `f + c >= 0 || g + d >= 0` on two terms, with its
/// key and the constants `c` and `d` of the terms in the key's order.
fn pair_of(g: &Formula) -> Option<(PairKey, Int, Int)> {
    let Formula::Or(gs) = g else { return None };
    let [Formula::Con(a), Formula::Con(b)] = &gs[..] else {
        return None;
    };
    if a.rel != Rel::Ge || b.rel != Rel::Ge || a.lin.terms == b.lin.terms {
        return None;
    }
    let (a, b) = if a.lin.terms < b.lin.terms {
        (a, b)
    } else {
        (b, a)
    };
    Some((
        (a.lin.terms.clone(), b.lin.terms.clone()),
        a.lin.constant.clone(),
        b.lin.constant.clone(),
    ))
}

/// A conjunction of formulas, `true` when empty.
#[derive(Clone, Debug, Default)]
pub struct Conjuncts {
    /// The conjuncts. `false` is the set of `false` alone.
    set: OrdSet<Arc<Formula>>,
    /// Of the constraints on each term with each relation, the one kept: a map for each
    /// relation ([`tight_at`]), keyed by the term alone, so that a lookup reads the
    /// constraint's own term and makes no key. Each key is shared, so that a copy of it, as a
    /// path copy of the persistent map makes for each key of a node it changes, costs a
    /// reference count and not the term (item PERF-conjuncts-term-keys).
    // Complexity tradeoff: a key `(BTreeMap<Atom, Int>, Rel)` held by value was cloned with
    // each key a path copy copies, O(t) for a term of t atoms, up to 16 keys a node and one
    // node a level, and each lookup cloned the term to make its key; behind an `Arc`, keyed by
    // the term within the map of its relation, a path copy is O(1) per key and a lookup clones
    // nothing. The order of each map is the order of the terms, as before within a relation,
    // and the maps are only looked up, never walked, so no answer changes. One `Arc` per
    // constraint kept. COMPLEXITY.md C46.
    tight: [Tight; 2],
    /// Of the disjunctions of two constraints on each pair of terms, those that no other
    /// implies ([`Conjuncts::pair`]). Each key is shared, as in `tight`.
    // Complexity tradeoff: a `PairKey` held by value was cloned with each key a path copy
    // copies, O(t) for terms of t atoms; behind an `Arc` it is O(1). A lookup still builds the
    // key from the disjunction ([`pair_of`]), O(t), once per disjunction added or removed, and
    // the `Arc` is made only for a key not yet in the map. Keys compare by the terms they
    // hold, so the order is unchanged. COMPLEXITY.md C46.
    pairs: OrdMap<Arc<PairKey>, Front>,
    /// The conjuncts that mention each name, alone or in a product.
    users: Uses<Arc<Formula>>,
    /// The equality constraints (`Rel::Eq`) that mention each name, so [`reach_eqs`] skips
    /// inequalities and disjunctions in O(1) when searching for Karr's join equalities.
    // Complexity tradeoff: naive version, `reach` with `is_eq` walked every conjunct in
    // `users.of(&n)` for each seed name at every join, O(k) per join and O(k^2) over k
    // disjunctions on the same names (split4: 16,778 iterations at k = 64 vs 314 at k = 8;
    // box_cases: 8,192 vs 128). Used: a persistent `Uses` index holding only `Rel::Eq`
    // constraints, O(s log e) per equality added/removed and O(1) when none exist.
    eq_users: Uses<Arc<Formula>>,
    /// The last change to `users`, `moving` and `free`, which share a name's set while they
    /// hold the same conjuncts there ([`Last`]).
    last: Last<Arc<Formula>>,
    /// The blocks of the conjuncts: the forest of the conjuncts of no star, and each star's
    /// conjuncts as a block of its own outside it ([`Blocks::detach`]).
    blocks: Blocks,
    /// The stars and what keeps them current, apart so that a conjunction is small to move.
    index: Box<StarIndex>,
}

/// Two names, in order.
type NamePair = (Arc<str>, Arc<str>);

/// A map keyed by name that is read only by key, never in order: the fields of [`StarIndex`]
/// and [`Admit`] of this type.
// Complexity tradeoff: naive version, an `OrdMap` keyed by name, O(log n) comparisons of
// two names a lookup, each a `memcmp`: on the bench
// `linked::bench::stars_formed_in_the_block_of_a_satellite_take_time_near_the_block`,
// `Arc<str>` comparison and `memcmp` took about 20% of the instructions and grew faster than
// the run (Gemini seat's callgrind, PERF-satellite-random-under9-redesign). Used: a persistent
// hash map (imbl `GenericHashMap`), one hash of the name (O(its length)) and one comparison
// on a match, O(1) expected a lookup. Correct only where no code reads the map's order:
// every use of these fields is `get`, `get_mut`, `contains_key`, `insert`, `remove`,
// `entry` or a sum over `values` (checked by reading each use, PERF-satellite-lookup-hash);
// the maps inside them stay `OrdMap`, since their keys are read in order. The keys are a
// program's names, so the hasher is the seeded `TextState` (DRY-sorted-structures-2 job 3; it
// was `FxBuildHasher`, with no seed, which let a program choose names that share a slot):
// equality, union and lookup of two such maps read keys, never the layout, so each map may
// draw its own seed, and no result reads the order. Only the maps read far
// more often than written are hashed: a write to a shared hash map copies a node of up to 32
// entries, where an `OrdMap` copies a leaf of a few, so hashing `whys`, `ties`, `near` and
// the `Uses` maps as well lowered the satellite bench to 0.805 of the instructions but raised
// the chain and ladder benches of linked/bench.rs by up to 1.062 in instructions and 1.151
// in bytes; with these four alone the satellite bench is 0.980 and no measured bench rose.
// COMPLEXITY.md row PERF-satellite-lookup-hash.
type ByName<V> = GenericHashMap<Arc<str>, V, TextState, DefaultSharedPtr>;

/// The class of a star of two hubs or more ([`Conjuncts::star`]): its conjuncts with the leaf
/// written [`LEAF`], in order. Two stars of one class have the same hubs and the same
/// conjuncts among them ([`Conjuncts::core`]), so their leaves differ only in their own
/// products ([`Conjuncts::class_core`]).
pub type Class = Arc<[Arc<Formula>]>;

/// The name of the leaf in a [`Class`]: one no program writes, since `#` begins no name.
pub const LEAF: &str = "#leaf";

/// The family of a class ([`Class`]): when the class is one inequality in which the leaf has
/// the coefficient 1 or -1, as `#leaf >= n + m - 3`, the class with that constant made 0;
/// otherwise the class itself. The classes of one family have the same hubs and conjuncts
/// among them and differ only in that constant, so each gives its leaf the family's bound
/// moved by its constant ([`Conjuncts::class_core`]): one check of whether the bound moved
/// answers for the whole family.
pub fn family(c: &Class) -> Class {
    let leaf = Atom::Sym(Arc::from(LEAF));
    if let [g] = &**c
        && let Formula::Con(con) = &**g
        && con.rel == Rel::Ge
        && con.lin.terms.get(&leaf).is_some_and(Int::is_unit)
    {
        let lin = Lin {
            terms: con.lin.terms.clone(),
            constant: Int::ZERO,
        };
        return [Arc::new(Formula::Con(Con { lin, rel: Rel::Ge }))].into();
    }
    c.clone()
}

/// `g` with the name `x` written `to`.
fn renamed(g: &Formula, x: &str, to: &Arc<str>) -> Formula {
    g.map_cons(&|c| {
        let terms = c
            .lin
            .terms
            .iter()
            .map(|(a, k)| match a {
                Atom::Sym(n) if &**n == x => (Atom::Sym(to.clone()), k.clone()),
                _ => (a.clone(), k.clone()),
            })
            .collect();
        Formula::Con(Con {
            lin: Lin {
                terms,
                constant: c.lin.constant.clone(),
            },
            rel: c.rel,
        })
    })
}

/// The key `(x, y, a, c)` of a row `a x + b y + c >= 0` ([`extreme_bucket_key`]).
pub type RowKey = (Atom, Atom, Int, Int);

/// The key of a row `a x + b y + c >= 0` of two symbols, `(x, y, a, c)`: the rows that differ
/// only in `b` share it. `None` for any other constraint. The preimage scope keeps of each key
/// only the rows of least and greatest `b` in the formula it projects (`extreme_base` in
/// zedc-preimage's product.rs, which proves the others implied).
pub fn extreme_bucket_key(c: &Con) -> Option<RowKey> {
    let mut terms = c.lin.terms.iter();
    match (c.rel, terms.next(), terms.next(), terms.next()) {
        (Rel::Ge, Some((x @ Atom::Sym(_), a)), Some((y @ Atom::Sym(_), _)), None) => {
            Some((x.clone(), y.clone(), a.clone(), c.lin.constant.clone()))
        }
        _ => None,
    }
}

/// A set of conjuncts sorted so that a reader can take only the rows of least and greatest
/// `b` of each [`extreme_bucket_key`]: the free conjuncts at one name
/// ([`Conjuncts::free_rows`], read by `Scope::family_bound` in zedc-preimage's product.rs),
/// and the core of a block (`Block::rows` there, read by `Scope::project_block`).
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Rows {
    /// The conjuncts that are no rows of [`extreme_bucket_key`].
    pub other: OrdSet<Arc<Formula>>,
    /// The rows, by their key and then by `b`, the coefficient of the key's `y`.
    pub rows: OrdMap<RowKey, OrdMap<Int, Arc<Formula>>>,
}

impl Rows {
    /// The key and `b` of conjunct `g`, when it is a row of [`extreme_bucket_key`] with `b`
    /// not 0. Two rows of one key and one `b` are the same constraint, so `b` names the row
    /// within its key. A row with `b` 0 counts as no row, so that between the least and
    /// greatest `b` of a key, -1 and 1, no row of `b` 0 is left out (the proof at
    /// `Scope::project_block` uses this).
    fn row(g: &Formula) -> Option<(RowKey, Int)> {
        let Formula::Con(c) = g else {
            return None;
        };
        let k = extreme_bucket_key(c)?;
        let b = c.lin.terms[&k.1].clone();
        (b != Int::ZERO).then_some((k, b))
    }

    /// Adds conjunct `g`. O(log n).
    pub fn insert(&mut self, g: &Arc<Formula>) {
        match Rows::row(g) {
            Some((k, b)) => {
                self.rows.entry(k).or_default().insert(b, g.clone());
            }
            None => {
                self.other.insert(g.clone());
            }
        }
    }

    /// Removes conjunct `g`, dropping a key left empty. O(log n).
    pub fn remove(&mut self, g: &Arc<Formula>) {
        match Rows::row(g) {
            Some((k, b)) => {
                if let Some(bs) = self.rows.get_mut(&k) {
                    bs.remove(&b);
                    if bs.is_empty() {
                        self.rows.remove(&k);
                    }
                }
            }
            None => {
                self.other.remove(g);
            }
        }
    }

    /// Whether no conjunct is in the set.
    pub fn is_empty(&self) -> bool {
        self.rows.is_empty() && self.other.is_empty()
    }

    /// The conjuncts other than rows, then of each key the rows of least and greatest `b`
    /// (one row when they are the same). O(m) for `m` conjuncts and keys returned.
    pub fn ends(&self) -> impl Iterator<Item = &Arc<Formula>> {
        let ends = self.rows.values().flat_map(|bs| {
            let lo = bs.get_min().map(|(_, g)| g);
            let hi = bs.get_max().filter(|_| bs.len() > 1).map(|(_, g)| g);
            lo.into_iter().chain(hi)
        });
        self.other.iter().chain(ends)
    }

    /// Adds (`add`) or removes conjunct `g` at name `h` of `at`, dropping a name left empty.
    /// O(log n).
    fn change(at: &mut OrdMap<Arc<str>, Rows>, h: &Arc<str>, g: &Arc<Formula>, add: bool) {
        if add {
            at.entry(h.clone()).or_default().insert(g);
            return;
        }
        let Some(rows) = at.get_mut(h) else {
            return;
        };
        rows.remove(g);
        if rows.is_empty() {
            at.remove(h);
        }
    }
}

/// The stars of a conjunction ([`Conjuncts::star`]) and the indexes that keep them current.
#[derive(Clone, Debug, Default)]
struct StarIndex {
    /// The names of the shape of a leaf ([`Conjuncts::star`]), each with its shape.
    shapes: ByName<Arc<Shape>>,
    /// The other names some conjunct mentions, each with why it is not of that shape.
    whys: OrdMap<Arc<str>, Arc<Why>>,
    /// Of the names of `whys` with a `count`, those of each witness, by their own counts.
    witnessed: Uses<(usize, Arc<str>)>,
    /// The names of `shapes` of each hub, by their own counts.
    shaped: Uses<(usize, Arc<str>)>,
    /// The conjuncts at each name that a name of `shapes` other than it holds.
    owned: Uses<Arc<Formula>>,
    /// The conjuncts at each name of that name alone ([`alone`]).
    solo: Uses<Arc<Formula>>,
    /// The conjuncts at each name in neither `owned` nor `solo`, as last found.
    free: Uses<Arc<Formula>>,
    /// The conjuncts of `free` at each name, sorted into rows ([`Rows`]), kept with `free`
    /// at its one place of change (`Conjuncts::refree`).
    free_rows: OrdMap<Arc<str>, Rows>,
    /// Of each name, the other names of its `free` conjuncts of two names, each with how many
    /// mention it: of a satellite ([`Conjuncts::star`]), the names it relates to.
    ties: OrdMap<Arc<str>, OrdMap<Arc<str>, usize>>,
    /// Of each name, how many of its `free` conjuncts are of other than two names: a name
    /// with none is a satellite.
    wide: ByName<usize>,
    /// The other names each hub's `free` conjuncts mention, each with how many mention it;
    /// kept only at the hubs of `level`, so that a conjunct of many names costs no more than
    /// its names unless they are such hubs.
    near: OrdMap<Arc<str>, OrdMap<Arc<str>, usize>>,
    /// Of each name, the hubs whose `near` holds it.
    nearby: Uses<Arc<str>>,
    /// Of each satellite related to a hub it is near, one such hub: the one that needs the
    /// names the satellite relates to, while each other hub it is near needs this one
    /// ([`StarIndex::place`]).
    anchor: ByName<Arc<str>>,
    /// What each hub of `level` needs among the hubs of a leaf to admit it.
    admit: Admit,
    /// The leaves of the names of `shapes` of two hubs or more, by their hubs.
    sets: OrdMap<Hubs, OrdSet<Arc<str>>>,
    /// Of each hub set of `sets`, how many of its hubs do not admit it.
    refused: OrdMap<Hubs, usize>,
    /// The stars ([`Conjuncts::star`]): each leaf's block.
    stars: OrdMap<Arc<str>, BlockId>,
    /// The leaves of the stars of two hubs or more of each class ([`Class`]).
    classes: OrdMap<Class, OrdSet<Arc<str>>>,
    /// The class of each leaf of `classes`.
    class_of: OrdMap<Arc<str>, Class>,
    /// The classes of `classes` at each of their hubs.
    class_at: Uses<Class>,
    /// The classes of each family of the classes of `classes` ([`family`]).
    families: OrdMap<Class, OrdSet<Class>>,
    /// The families of `families` at each of their hubs.
    family_at: Uses<Class>,
    /// The conjuncts that mention each name, but those of the stars at it as a hub: those a
    /// move of the name makes due in a lazy scope ([`Conjuncts::moving`]).
    moving: Uses<Arc<Formula>>,
    /// The names a written constraint holds of, which are no leaves (`Scope::write`).
    pinned: OrdSet<Arc<str>>,
    /// The sides each name is bounded on, the upper side `true`, as the scope last stated
    /// them ([`Conjuncts::bound`]).
    bounded: OrdSet<(Arc<str>, bool)>,
}

/// The shape of a leaf ([`Conjuncts::star`]).
#[derive(Clone, Debug, PartialEq)]
struct Shape {
    /// Its conjuncts.
    gs: Vec<Arc<Formula>>,
    /// Its hubs: the other names its conjuncts mention, in order.
    hubs: Hubs,
    /// The side, the upper one `true`, that some conjunct of two hubs or more needs unbounded.
    far: Option<bool>,
    /// The number of its conjuncts.
    count: usize,
}

/// Why a name with conjuncts is not of the shape of a leaf: what a change must touch to make
/// it one, so that no other change looks at it again.
#[derive(Clone, Debug, PartialEq)]
struct Why {
    /// Conjuncts at the name that show it: only a removal of one of them can undo it.
    by: Vec<Arc<Formula>>,
    /// A name it shares the conjunct `by` with, of no more conjuncts than it: a witness that it
    /// is no leaf, which a rise of that name's count past its own undoes.
    count: Option<Arc<str>>,
    /// The side, the upper one `true`, whose bound a conjunct of two hubs or more needs
    /// unbounded.
    bound: Option<bool>,
    /// The number of its conjuncts.
    size: usize,
}

/// The work a change to the conjuncts leaves for [`Conjuncts::flush`].
#[derive(Default)]
struct Pending {
    /// The names whose shape may have changed.
    eval: BTreeSet<Arc<str>>,
    /// The conjuncts whose use or ownership changed: whether each is free at its names may
    /// have.
    free: BTreeSet<Arc<Formula>>,
    /// The conjuncts added, not yet in a block, each with the one it takes the place of.
    placed: Vec<(Arc<Formula>, Option<Arc<Formula>>)>,
    /// The needs and hits moved so far ([`Conjuncts::readmit`]): a hub set opened or closed
    /// moves the needs of satellites at other hubs.
    moves: Moves,
}

/// The hubs of a leaf of two hubs or more ([`Conjuncts::star`]), in order: the key the leaves
/// of one hub set share at each hub, so that a change at a hub costs its hub sets, not its
/// leaves.
type Hubs = Arc<[Arc<str>]>;

/// What each hub of a leaf of two hubs or more needs among the leaf's hubs to admit it
/// ([`Conjuncts::star`]).
#[derive(Clone, Debug, Default)]
struct Admit {
    /// Of each such hub, the names its `near` names need among a leaf's hubs, each with how
    /// many need it: a satellite its anchor, or at the anchor or when it has none the names it
    /// relates to other than the hub ([`StarIndex::place`]); any other name itself. The hub
    /// admits a leaf whose hubs hold all of them.
    needs: ByName<OrdMap<Arc<str>, usize>>,
    /// Of each such hub and hub set at it, how many of the hub's `needs` the set holds.
    hits: OrdMap<(Arc<str>, Hubs), usize>,
    /// The hub sets at each such hub, by their `hits` there.
    level: Uses<(usize, Hubs)>,
    /// The hub sets at each such hub that hold each other name.
    pair: OrdMap<NamePair, OrdSet<Hubs>>,
}

/// The values of [`Admit`] before a change, each recorded when it first moves.
#[derive(Default)]
struct Moves {
    /// Of each hub, its number of `needs`.
    lens: BTreeMap<Arc<str>, usize>,
    /// Of each hub and hub set at it, its `hits`.
    hits: BTreeMap<(Arc<str>, Hubs), usize>,
    /// The hub sets opened since: their hubs' admissions are counted afresh
    /// ([`Conjuncts::readmit`]), since needs may have moved before or after they opened.
    fresh: BTreeSet<Hubs>,
}

impl Admit {
    /// Counts one more (`up`) or one fewer name of hub `h`'s `near` that needs `z`; when `z`
    /// comes or goes, each hub set at `h` that holds it gains or loses a hit. In O(log n),
    /// and O(log n) for each such hub set.
    fn need(&mut self, h: &Arc<str>, z: &Arc<str>, up: bool, log: &mut Moves) {
        let Some(needs) = self.needs.get_mut(h) else {
            unreachable!("needs are kept at each hub of a hub set")
        };
        let (c, len) = (needs.get(z).copied().unwrap_or(0), needs.len());
        match (up, c) {
            (true, _) => {
                needs.insert(z.clone(), c + 1);
            }
            (false, 1) => {
                needs.remove(z);
            }
            (false, _) => {
                needs.insert(z.clone(), c - 1);
            }
        }
        if c != usize::from(!up) {
            return;
        }
        log.lens.entry(h.clone()).or_insert(len);
        for hs in self.pair.get(&(h.clone(), z.clone())).into_iter().flatten() {
            let key = (h.clone(), hs.clone());
            let k = self.hits[&key];
            let k2 = if up { k + 1 } else { k - 1 };
            self.level.remove(h, &(k, hs.clone()));
            self.level.add(h, &(k2, hs.clone()));
            log.hits.entry(key.clone()).or_insert(k);
            self.hits.insert(key, k2);
        }
    }
}

impl StarIndex {
    /// Counts in (`up`) or out the needs of satellite `y` at each hub it is near
    /// ([`Admit::needs`]), as `ties`, `nearby` and `anchor` now stand. A hub `h` near `y`
    /// admits a leaf whose hubs hold the names `y` relates to other than `h`: as `h` is one
    /// of the hubs, all of those names, the same test at each hub `y` is near. So when `y` is
    /// related to some hub it is near, its anchor `a`, `a` needs the names `y` relates to and
    /// each other hub near `y` needs `a` alone: when every hub of a leaf admits it, and one
    /// of them is near `y`, `a` is among them and admits it, so they hold all the names `y`
    /// relates to; and when they hold those names, they hold every need, `a` among them. So
    /// the leaves all of whose hubs admit them are those of each hub needing all of `y`'s
    /// names, and `y` holds `k - 1 + m` needs for `k` hubs near it and `m` names related, not
    /// `k m`. Without an anchor each hub near `y` needs all of them, which holds only within
    /// a flush: a hub of a hub set is no leaf, since a leaf's hubs have more conjuncts than
    /// it ([`Conjuncts::shape_of`]), so no leaf holds a conjunct free at such a hub `h`, and
    /// a conjunct of `h` and `y` free at `h` is free at `y` too once `refree` has seen it,
    /// which puts `h` in `ties[y]` and makes `h` an anchor. In O(log n) for each.
    ///
    /// Complexity tradeoff: naive version, each hub near `y` needs every name `y` relates
    /// to, `k m` needs for `k` hubs and `m` names, so a satellite related to `d` hubs costs
    /// O(d²) needs (measured d(d - 1): 132 and 9,120 at `d` 12 and 96, before STAR-hub-set);
    /// a satellite's names kept once as a set would instead make each admission a test of
    /// one set within another at each hub set at each hub. Used: the anchor holds the `m`
    /// names and each other hub the anchor alone, `k - 1 + m` needs, O((k + m) log n) per
    /// move of the anchor, and admission counted per name, one membership test per name.
    /// Tradeoffs: none in the answers (exact, as argued above); memory for `anchor` and the
    /// hit counts of [`Admit`]; an anchor that moves re-counts the satellite's needs. Test
    /// `l01_39_scope_relations::linked::a_satellite_of_every_hub_costs_its_related_names_once`
    /// (2d - 1 needs). COMPLEXITY.md row C37.
    fn place(&mut self, y: &Arc<str>, up: bool, log: &mut Moves) {
        let StarIndex {
            ties,
            nearby,
            anchor,
            admit,
            ..
        } = self;
        let a = anchor.get(y);
        for h in nearby.of(y) {
            match a {
                Some(a) if a != h => admit.need(h, a, up, log),
                _ => {
                    for z in ties.get(y).into_iter().flat_map(OrdMap::keys) {
                        if z != h {
                            admit.need(h, z, up, log);
                        }
                    }
                }
            }
        }
    }

    /// Picks the anchor of satellite `y`, which has no needs counted ([`StarIndex::place`]):
    /// the first name it relates to that is a hub it is near, if any; and counts its needs.
    /// In O(log n) for each name it relates to, and as `place` costs.
    fn repick(&mut self, y: &Arc<str>, log: &mut Moves) {
        let StarIndex {
            ties,
            nearby,
            anchor,
            ..
        } = &mut *self;
        match ties
            .get(y)
            .into_iter()
            .flat_map(OrdMap::keys)
            .find(|z| nearby.has(y, z))
        {
            Some(a) => anchor.insert(y.clone(), a.clone()),
            None => anchor.remove(y),
        };
        self.place(y, true, log);
    }

    /// Picks the anchor of satellite `y` again, its needs counted out and back in
    /// ([`StarIndex::repick`]): after a change that makes or takes away its anchor.
    fn reanchor(&mut self, y: &Arc<str>, log: &mut Moves) {
        self.place(y, false, log);
        self.repick(y, log);
    }
}

/// Whether `g` is `±x ± y ± … + c >= 0`, a bound on a sum of two names or more, each of
/// coefficient one or minus one, such as a difference of two names. The negation of one,
/// `!(x - y + c >= 0)`, is one as well, `y - x - c - 1 >= 0`.
pub fn unit_sum(g: &Formula) -> bool {
    let c = match g {
        Formula::Con(c) => c,
        Formula::Not(n) => match &**n {
            Formula::Con(c) => c,
            _ => return false,
        },
        _ => return false,
    };
    let (one, minus) = (Int::ONE, Int::from(-1i64));
    c.rel == Rel::Ge
        && c.lin.terms.len() >= 2
        && c.lin
            .terms
            .iter()
            .all(|(a, k)| matches!(a, Atom::Sym(_)) && (*k == one || *k == minus))
}

/// An edge of a difference constraint: `to <= from + weight`, `None` standing for the value 0
/// (Shostak's zero variable `v0`, sec. 2; Shostak 1981, doi:10.1145/322276.322288, read
/// 2026-11-21; for these rows the graph is its own closure, sec. 4; see the crate's `lib.rs`,
/// "References"), so that a bound is an edge to or from it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Edge {
    /// The name the edge leaves, or `None` for 0.
    pub from: Option<Arc<str>>,
    /// The name the edge enters, or `None` for 0.
    pub to: Option<Arc<str>>,
    /// The weight.
    pub weight: Int,
}

/// The edges of `g` when it is a difference constraint or a bound: `x - y + k >= 0`,
/// `±x + k >= 0`, their equalities, each an edge both ways, and the negation of one of the
/// inequalities, `!(t >= 0)` being `-t - 1 >= 0`. `None` for any other conjunct.
pub fn edges(g: &Formula) -> Option<(Edge, Option<Edge>)> {
    let (lin, rel) = match g {
        Formula::Con(c) => (c.lin.clone(), c.rel),
        Formula::Not(n) => match &**n {
            Formula::Con(c) if c.rel == Rel::Ge => (
                c.lin.times(Int::from(-1i64)).plus(&Lin::constant(-1)),
                Rel::Ge,
            ),
            _ => return None,
        },
        _ => return None,
    };
    let mut ends: [(Option<Arc<str>>, bool); 2] = [(None, true), (None, false)];
    let mut found = [false; 2];
    for (a, k) in &lin.terms {
        let Atom::Sym(n) = a else { return None };
        if !k.is_unit() {
            return None;
        }
        let side = usize::from(!k.is_positive());
        if found[side] {
            return None;
        }
        found[side] = true;
        ends[side].0 = Some(n.clone());
    }
    if !found.contains(&true) {
        return None;
    }
    // `x - y + k` with `x` or `y` possibly 0: the edge `x → y` of weight `k`.
    let [(x, _), (y, _)] = ends;
    let k = lin.constant;
    let back = (rel == Rel::Eq).then(|| Edge {
        from: y.clone(),
        to: x.clone(),
        weight: -&k,
    });
    Some((
        Edge {
            from: x,
            to: y,
            weight: k,
        },
        back,
    ))
}

impl PartialEq for Conjuncts {
    fn eq(&self, other: &Conjuncts) -> bool {
        self.set == other.set
    }
}

/// The name `g` holds of alone, when that name is its one atom: a bound or a class of the name
/// that relates it to no other name or atom.
fn alone(g: &Formula) -> Option<Arc<str>> {
    let atoms = g.atoms();
    match atoms.first() {
        Some(Atom::Sym(n)) if atoms.len() == 1 => Some(n.clone()),
        _ => None,
    }
}

/// The names `f` mentions, alone or in a product.
pub fn names(f: &Formula) -> BTreeSet<Arc<str>> {
    names_of_atoms(&f.atoms())
}

/// The names the atoms `atoms` mention, alone or in a product: [`names`] for a caller that
/// already holds a formula's atoms, so that they are not collected twice.
fn names_of_atoms(atoms: &BTreeSet<Atom>) -> BTreeSet<Arc<str>> {
    let mut out = BTreeSet::new();
    for a in atoms {
        match a {
            Atom::Sym(n) => {
                out.insert(n.clone());
            }
            Atom::Product(x, y) => {
                for f in [x, y] {
                    if let Factor::Sym(n) = f {
                        out.insert(n.clone());
                    }
                }
            }
            Atom::Aux(_) => {}
        }
    }
    out
}

impl Conjuncts {
    /// Whether the conjunction is `true`.
    pub fn is_top(&self) -> bool {
        self.set.is_empty()
    }

    /// Whether the conjunction is `false`.
    pub fn is_bottom(&self) -> bool {
        self.set.iter().next().is_some_and(|f| is_false(f))
    }

    /// The conjuncts, in the order of formulas.
    pub fn set(&self) -> &OrdSet<Arc<Formula>> {
        &self.set
    }

    /// The conjuncts that mention `name`.
    pub fn mentioning(&self, name: &str) -> impl Iterator<Item = &Arc<Formula>> {
        self.users.of(name)
    }

    /// The names some conjunct mentions.
    pub fn names(&self) -> impl Iterator<Item = &Arc<str>> {
        self.users.names()
    }

    /// The blocks of the conjuncts.
    pub fn blocks(&self) -> &Blocks {
        &self.blocks
    }

    /// The block of the star of which `x` is the leaf, if any. A leaf is a name no written
    /// constraint holds of ([`Conjuncts::pin`]) each conjunct at which is a constraint
    /// `a * x + b1 * y1 + … + c >= 0` of names alone with at least one other name, its hubs,
    /// or a disjunction of such constraints, such as `x < n || x < m`, of which some may be of
    /// `x` alone, such as `x >= 5` of `x >= n || x >= 5`, and one at least is not, which holds
    /// for `x` far enough on the side each of its constraints does;
    /// `a` is of one sign at every conjunct, so is each hub's coefficient, each hub is
    /// mentioned by more conjuncts than `x`, and where a conjunct mentions two hubs or more,
    /// `x` is unbounded on the side away from it ([`Conjuncts::bound`]). The leaf's conjuncts
    /// are a star when it has one hub or each of its hubs admits it: every conjunct at the hub
    /// is a leaf's, or of the hub alone (`alone`), such as a bound on it, or is free at it
    /// and each of its other names is a hub of `x`, such as `m` in `n >= m` for the hubs of
    /// `x >= n && x >= m`, or a satellite whose other related names are hubs of `x`. A
    /// satellite is a name each of whose free conjuncts, those neither a leaf's nor of it
    /// alone, mentions it and one other name, the names it relates to: `y` of
    /// `y >= n && y < m` for the hubs `n` and `m`. A conjunct is the leaf's of one name at
    /// most, since its hubs have more conjuncts than it.
    ///
    /// A star bounds its leaf on one side only, the side its hubs' least or greatest values
    /// bound it from, and a conjunct of two hubs or more holds for a large enough `x`: the
    /// star's projection onto its hubs is a bound on each hub alone, and so is the projection
    /// of a leaf's conjuncts at a hub or a satellite, and its other conjuncts hold of it alone,
    /// or of the leaf's hubs and satellites, as each free conjunct of a satellite relates it to
    /// a hub at which that conjunct is free. The hubs of a star of more than one then range,
    /// with the satellites, over their products and the free conjuncts at the hubs
    /// ([`Conjuncts::core`]), a closed set, with which the star is projected, and a
    /// star of one hub lies on no cycle, so in both the projection onto `x` is the projection
    /// of the whole relation, and a move of a hub changes `x` alone and cuts it to a
    /// half-line that holds its greatest or least member, which empties nothing. A move of a
    /// satellite changes the leaves of the stars at the hubs it relates to
    /// ([`Conjuncts::around`]). A name related to two hubs by one conjunct, such as `y` of
    /// `n + m <= y <= n + m + 1`, is no satellite, so it keeps the hubs from admitting a
    /// leaf not of it. A star is a block of its own outside the forest
    /// ([`Blocks::detach`]).
    pub fn star(&self, x: &str) -> Option<BlockId> {
        self.index.stars.get(x).copied()
    }

    /// The conjuncts block `b` is projected with: its own, and when it is a star of two hubs
    /// or more, the free conjuncts at its hubs, which mention only its hubs and the
    /// satellites they admit, each of whose free conjuncts is among them
    /// ([`Conjuncts::star`]). In time near their number.
    pub fn core(&self, b: BlockId) -> Vec<Arc<Formula>> {
        let mut gs: BTreeSet<Arc<Formula>> = self.blocks.members(b).cloned().collect();
        if self.blocks.is_apart(b) {
            let ns: BTreeSet<Arc<str>> = gs.iter().flat_map(|g| names(g)).collect();
            // The leaf's conjuncts are free at it; a star of one hub has two names.
            if ns.len() > 2 {
                for n in &ns {
                    gs.extend(self.index.free.of(n).cloned());
                }
            }
        }
        gs.into_iter().collect()
    }

    /// The families ([`family`]) of the classes of the stars of two hubs or more whose
    /// projection reads `g` as a conjunct among their hubs ([`Conjuncts::core`]): those at each
    /// name `g` is free at. In time near the families at those names, not their classes.
    pub fn classed(&self, g: &Arc<Formula>) -> BTreeSet<Class> {
        let mut out = BTreeSet::new();
        for n in names(g) {
            if self.index.free.has(&n, g) {
                out.extend(self.index.family_at.of(&n).cloned());
            }
        }
        out
    }

    /// The conjuncts each star of class `c` is projected with ([`Conjuncts::core`]), its leaf
    /// written [`LEAF`]: the class's conjuncts and those among its hubs. `None` when no star is
    /// of the class. In time near their number.
    pub fn class_core(&self, c: &Class) -> Option<Vec<Arc<Formula>>> {
        self.index.classes.get(c)?;
        let mut gs: BTreeSet<Arc<Formula>> = c.iter().cloned().collect();
        let ns: BTreeSet<Arc<str>> = c.iter().flat_map(|g| names(g)).collect();
        for n in ns.iter().filter(|n| &***n != LEAF) {
            gs.extend(self.index.free.of(n).cloned());
        }
        Some(gs.into_iter().collect())
    }

    /// The classes of family `f` ([`family`]).
    pub fn family_classes(&self, f: &Class) -> impl Iterator<Item = &Class> {
        self.index.families.get(f).into_iter().flatten()
    }

    /// The free conjuncts at `n` ([`Conjuncts::core`]) as their persistent set ([`Uses::set`]).
    pub fn free_set(&self, n: &str) -> Option<&OrdSet<Arc<Formula>>> {
        self.index.free.set(n)
    }

    /// The free conjuncts at `n` ([`Conjuncts::free_set`]) sorted into rows ([`Rows`]), in
    /// O(log n); `None` when there are none.
    pub fn free_rows(&self, n: &str) -> Option<&Rows> {
        self.index.free_rows.get(n)
    }

    /// The leaves of the stars of class `c`.
    pub fn class_leaves(&self, c: &Class) -> impl Iterator<Item = &Arc<str>> {
        self.index.classes.get(c).into_iter().flatten()
    }

    /// The classes of the stars of two hubs or more of which `h` is a hub.
    pub fn classes_at(&self, h: &str) -> impl Iterator<Item = &Class> {
        self.index.class_at.of(h)
    }

    /// The class of each star of two hubs or more, by its leaf ([`Conjuncts::class_of`]), as
    /// the persistent map, which two relations of one scope compare by its difference.
    pub fn classes_of(&self) -> &OrdMap<Arc<str>, Class> {
        &self.index.class_of
    }

    /// The class of the star of leaf `x`, when it has two hubs or more.
    pub fn class_of(&self, x: &str) -> Option<&Class> {
        self.index.class_of.get(x)
    }

    /// Records the star of leaf `x` and conjuncts `gs` in its class, when it has two hubs or
    /// more ([`Class`]). In O(log n) per conjunct, and per hub when the class is new.
    fn enclass(&mut self, x: &Arc<str>, gs: &[Arc<Formula>], hubs: &[Arc<str>]) {
        if hubs.len() < 2 {
            return;
        }
        let leaf: Arc<str> = Arc::from(LEAF);
        let mut key: Vec<Arc<Formula>> =
            gs.iter().map(|g| Arc::new(renamed(g, x, &leaf))).collect();
        key.sort_unstable();
        let key: Class = key.into();
        let leaves = self.index.classes.entry(key.clone()).or_default();
        let new = leaves.is_empty();
        leaves.insert(x.clone());
        if new {
            for h in hubs {
                self.index.class_at.add(h, &key);
            }
            let f = family(&key);
            let classes = self.index.families.entry(f.clone()).or_default();
            if classes.is_empty() {
                for h in hubs {
                    self.index.family_at.add(h, &f);
                }
            }
            classes.insert(key.clone());
        }
        self.index.class_of.insert(x.clone(), key);
    }

    /// Forgets the class of the star of leaf `x`, if it has one ([`Conjuncts::enclass`]).
    fn unclass(&mut self, x: &str) {
        let Some(key) = self.index.class_of.remove(x) else {
            return;
        };
        let Some(leaves) = self.index.classes.get_mut(&key) else {
            return;
        };
        leaves.remove(x);
        if leaves.is_empty() {
            self.index.classes.remove(&key);
            let hubs: BTreeSet<Arc<str>> = key.iter().flat_map(|g| names(g)).collect();
            for h in hubs.iter().filter(|h| &***h != LEAF) {
                self.index.class_at.remove(h, &key);
            }
            let f = family(&key);
            if let Some(classes) = self.index.families.get_mut(&f) {
                classes.remove(&key);
                if classes.is_empty() {
                    self.index.families.remove(&f);
                    for h in hubs.iter().filter(|h| &***h != LEAF) {
                        self.index.family_at.remove(h, &f);
                    }
                }
            }
        }
    }

    /// How many names the hubs of hub sets need, summed over the hubs ([`Admit::needs`]): what
    /// a scaling test counts to show a satellite costs near the names it relates to.
    #[doc(hidden)]
    pub fn needs_held(&self) -> usize {
        self.index.admit.needs.values().map(OrdMap::len).sum()
    }

    /// The leaf and block of each star ([`Conjuncts::star`]).
    pub fn stars(&self) -> &OrdMap<Arc<str>, BlockId> {
        &self.index.stars
    }

    /// The conjuncts of the stars whose hub is `y`.
    pub fn hanging(&self, y: &str) -> impl Iterator<Item = &Arc<Formula>> {
        self.blocks.hung.of(y)
    }

    /// The leaves of the stars of two hubs or more whose projection reads a conjunct at `y`
    /// ([`Conjuncts::core`]): of a satellite, the stars at the hubs it relates to, which a move
    /// of `y` changes though no conjunct of theirs mentions it. Of any other name, none but
    /// the stars whose hub it is, which [`Conjuncts::hanging`] finds: a hub admits a name near
    /// it that is no satellite only as a hub of the leaf. In time near the hubs `y` is near,
    /// the classes at them, and the leaves of those classes.
    pub fn around(&self, y: &str) -> BTreeSet<Arc<str>> {
        if self.index.wide.get(y).is_some_and(|w| *w > 0) {
            return BTreeSet::new();
        }
        let classes: BTreeSet<&Class> = (self.index.nearby.of(y))
            .flat_map(|h| self.index.class_at.of(h))
            .collect();
        classes
            .iter()
            .flat_map(|c| self.class_leaves(c).cloned())
            .collect()
    }

    /// The conjuncts that mention `name` but those of the stars whose hub it is: those a move
    /// of `name` makes due in a scope that leaves its stars' leaves to be settled when read.
    pub fn moving(&self, name: &str) -> impl Iterator<Item = &Arc<Formula>> {
        self.index.moving.of(name)
    }

    /// The conjuncts a move of `name` makes due: [`Conjuncts::moving`] when `lazy`, else
    /// [`Conjuncts::mentioning`].
    pub fn moved(&self, name: &str, lazy: bool) -> impl Iterator<Item = &Arc<Formula>> {
        if lazy {
            &self.index.moving
        } else {
            &self.users
        }
        .of(name)
    }

    /// Records whether a written constraint holds of `name`: such a name is no leaf, since an
    /// enumeration reads it.
    pub fn pin(&mut self, name: &Arc<str>, on: bool) {
        let changed = if on {
            self.index.pinned.insert(name.clone()).is_none()
        } else {
            self.index.pinned.remove(name).is_some()
        };
        if changed {
            let mut p = Pending::default();
            p.eval.insert(name.clone());
            self.flush(p);
        }
    }

    /// Records whether `name` keeps its tree from projection by shortest paths
    /// ([`Blocks::differences_only`]), as the scope says: its integers lie in a class, or have
    /// holes wider than the scope's potential holds with. In O(log n).
    pub fn gapped(&mut self, name: &Arc<str>, on: bool) {
        self.blocks.gap(name, on);
    }

    /// Whether the tree of blocks that holds `name` holds only difference constraints and
    /// bounds of names none of which keeps it from shortest paths
    /// ([`Blocks::differences_only`]); true
    /// when no conjunct of the forest mentions `name`.
    pub fn differences_only_at(&self, name: &str) -> bool {
        self.blocks
            .tree_of_name(name)
            .is_none_or(|t| self.blocks.differences_only(t))
    }

    /// Records whether `name` is bounded below and above, as the scope's product of it says:
    /// a leaf with a conjunct of two hubs or more is unbounded on the side away from it
    /// ([`Conjuncts::star`]). A name never stated is unbounded. In O(log n), and the name's
    /// conjuncts when a side its shape reads changes.
    pub fn bound(&mut self, name: &Arc<str>, below: bool, above: bool) {
        let mut p = Pending::default();
        for (side, on) in [(false, below), (true, above)] {
            let key = (name.clone(), side);
            let changed = if on {
                self.index.bounded.insert(key).is_none()
            } else {
                self.index.bounded.remove(&key).is_some()
            };
            let reads = self
                .index
                .shapes
                .get(name)
                .is_some_and(|s| s.far == Some(side))
                || self
                    .index
                    .whys
                    .get(name)
                    .is_some_and(|w| w.bound == Some(side));
            if changed && reads {
                p.eval.insert(name.clone());
            }
        }
        if !p.eval.is_empty() {
            self.flush(p);
        }
    }

    /// Whether a written constraint holds of `name` ([`Conjuncts::pin`]).
    pub fn pinned(&self, name: &str) -> bool {
        self.index.pinned.contains(name)
    }

    /// Whether `name` is bounded above (`above`) or below, as last stated
    /// ([`Conjuncts::bound`]).
    pub fn bounded(&self, name: &Arc<str>, above: bool) -> bool {
        self.index.bounded.contains(&(name.clone(), above))
    }

    /// The shape of `x`, a name some conjunct mentions, by the counts, pins and bounds as they
    /// are ([`Conjuncts::star`]), or why it has none: in time near its conjuncts.
    fn shape_of(&self, x: &Arc<str>) -> Result<Shape, Why> {
        let count = self.users.count(x);
        let why = |by: Vec<Arc<Formula>>| Why {
            by,
            count: None,
            bound: None,
            size: count,
        };
        if self.index.pinned.contains(x) {
            return Err(why(Vec::new()));
        }
        let at = Atom::Sym(x.clone());
        // The sign of `x`'s coefficient, and of each hub's, with a conjunct that shows it.
        let mut sign: Option<(bool, &Arc<Formula>)> = None;
        let mut hubs: BTreeMap<&Arc<str>, (bool, &Arc<Formula>)> = BTreeMap::new();
        let mut far = None;
        for g in self.users.of(x) {
            // A constraint, or a disjunction of constraints each of which mentions `x`: as each
            // holds for `x` far enough on one side, so does their disjunction.
            let one = std::slice::from_ref(&**g);
            let parts: &[Formula] = match &**g {
                Formula::Con(_) => one,
                Formula::Or(gs) if gs.len() > 1 => gs,
                _ => return Err(why(vec![g.clone()])),
            };
            let mut others: BTreeSet<&Arc<str>> = BTreeSet::new();
            for part in parts {
                let Formula::Con(c) = part else {
                    return Err(why(vec![g.clone()]));
                };
                let Some(a) = c.lin.terms.get(&at) else {
                    return Err(why(vec![g.clone()]));
                };
                // A term other than a name is found in the loop over the terms below, so that
                // the witness there is found first (see the tradeoff below).
                if c.rel != Rel::Ge {
                    return Err(why(vec![g.clone()]));
                }
                let up = a.is_positive();
                match sign {
                    Some((s, h)) if s != up => return Err(why(vec![g.clone(), h.clone()])),
                    Some(_) => {}
                    None => sign = Some((up, g)),
                }
                for (a, b) in &c.lin.terms {
                    let Atom::Sym(h) = a else {
                        return Err(why(vec![g.clone()]));
                    };
                    if h == x {
                        continue;
                    }
                    others.insert(h);
                    match hubs.get(h) {
                        Some(&(s, k)) if s != b.is_positive() => {
                            return Err(why(vec![g.clone(), k.clone()]));
                        }
                        Some(_) => {}
                        None => {
                            hubs.insert(h, (b.is_positive(), g));
                        }
                    }
                    // A name of no more conjuncts than `x` shows that `x` is no leaf, whatever the
                    // rest of its conjuncts say.
                    // Complexity tradeoff: the naive way read every term of every conjunct of
                    // `x` before taking the witness, and first read them all once more to see
                    // that each is a name: Θ(k log k) for each of the `k` names of
                    // `z0 + … + z(k-1) >= 0`, each found again when the row comes: Θ(k² log k)
                    // for the whole assume (4.2 s at k = 2048 once the projection was linear).
                    // Stopping at the first witness, with a term other than a name found in the
                    // same loop, reads O(1) terms of such a row for each name, and the leaf's
                    // shape found is the same, since a shape needs no witness and every term is
                    // still read before one is given; only which reason a name of no shape
                    // keeps may differ, and each reason is one that only its own change can
                    // undo ([`Why`]). Still above:
                    // a name whose conjuncts' other names all have more conjuncts than it,
                    // with a sign or a side read last, is read whole. Test:
                    // `l01_39_reduced_product::scaling::a_sum_over_many_names_is_assumed_in_time_near_linear`.
                    // COMPLEXITY.md row F154.
                    if self.users.count(h) <= count {
                        return Err(Why {
                            count: Some(h.clone()),
                            ..why(vec![g.clone()])
                        });
                    }
                }
                if c.lin.terms.len() == 1 && parts.len() == 1 {
                    return Err(why(vec![g.clone()]));
                }
            }
            if others.is_empty() {
                return Err(why(vec![g.clone()]));
            }
            // `x` is bounded by `g` below when `up`, so a large enough `x` meets it when `x`
            // is unbounded above.
            if others.len() > 1 {
                let up = sign.is_some_and(|(s, _)| s);
                if self.index.bounded.contains(&(x.clone(), up)) {
                    return Err(Why {
                        bound: Some(up),
                        ..why(vec![g.clone()])
                    });
                }
                far = Some(up);
            }
        }
        Ok(Shape {
            gs: self.users.of(x).cloned().collect(),
            hubs: hubs.into_keys().cloned().collect(),
            far,
            count,
        })
    }

    /// Takes `x`'s shape or `Why` out of the indexes; each conjunct whose ownership changes is
    /// put in `p` at its names. Every name to be found again is taken out first
    /// ([`Conjuncts::flush`]): a conjunct whose leaf changes in one flush is then owned by the
    /// new leaf alone.
    fn unshape(&mut self, x: &Arc<str>, p: &mut Pending) {
        if let Some(old) = self.index.shapes.remove(x) {
            for g in &old.gs {
                for h in names(g).into_iter().filter(|h| h != x) {
                    self.index.owned.remove(&h, g);
                }
                p.free.insert(g.clone());
            }
            for h in old.hubs.iter() {
                self.index.shaped.remove(h, &(old.count, x.clone()));
            }
            if old.hubs.len() > 1
                && let Some(leaves) = self.index.sets.get_mut(&old.hubs)
            {
                leaves.remove(x);
                if leaves.is_empty() {
                    self.index.sets.remove(&old.hubs);
                    self.close(&old.hubs, &mut p.moves);
                }
            }
        }
        if let Some(old) = self.index.whys.remove(x)
            && let Some(h) = &old.count
        {
            self.index.witnessed.remove(h, &(old.size, x.clone()));
        }
    }

    /// Finds `x`'s shape, its old one taken out ([`Conjuncts::unshape`]), and indexes it; each
    /// conjunct whose ownership changes is put in `p` at its names.
    fn reshape(&mut self, x: &Arc<str>, p: &mut Pending) {
        if self.users.count(x) == 0 {
            return;
        }
        match self.shape_of(x) {
            Ok(s) => {
                for g in &s.gs {
                    for h in names(g).into_iter().filter(|h| h != x) {
                        self.index.owned.add(&h, g);
                    }
                    p.free.insert(g.clone());
                }
                for h in s.hubs.iter() {
                    self.index.shaped.add(h, &(s.count, x.clone()));
                }
                if s.hubs.len() > 1 {
                    let leaves = self.index.sets.entry(s.hubs.clone()).or_default();
                    let fresh = leaves.is_empty();
                    leaves.insert(x.clone());
                    if fresh {
                        self.open(&s.hubs, &mut p.moves);
                    }
                }
                self.index.shapes.insert(x.clone(), Arc::new(s));
            }
            Err(w) => {
                if let Some(h) = &w.count {
                    self.index.witnessed.add(h, &(w.size, x.clone()));
                }
                self.index.whys.insert(x.clone(), Arc::new(w));
            }
        }
    }

    /// Indexes hub set `hs`, of a leaf that is the first of its hubs ([`Admit`]): each hub's
    /// `near` names are counted, when it had no hub set before, from its free conjuncts as
    /// last found, which `refree` then keeps. Its hubs' admissions are counted again by
    /// [`Conjuncts::readmit`], as the needs of satellites at other hubs may move later in the
    /// same change ([`StarIndex::place`]). In O(log n) for each hub and pair of hubs, and for
    /// each hub of no hub set before, as [`Conjuncts::view`] costs.
    fn open(&mut self, hs: &Hubs, log: &mut Moves) {
        for h in hs.iter() {
            self.view(h, log);
            let Admit {
                needs,
                hits,
                level,
                pair,
            } = &mut self.index.admit;
            let needs = needs.get(h);
            let held = |z: &&Arc<str>| *z != h && needs.is_some_and(|m| m.contains_key(*z));
            let k = hs.iter().filter(held).count();
            hits.insert((h.clone(), hs.clone()), k);
            level.add(h, &(k, hs.clone()));
            for z in hs.iter().filter(|z| *z != h) {
                pair.entry((h.clone(), z.clone()))
                    .or_default()
                    .insert(hs.clone());
            }
        }
        self.index.refused.insert(hs.clone(), 0);
        log.fresh.insert(hs.clone());
    }

    /// Forgets hub set `hs`, whose last leaf went ([`Conjuncts::open`]); a hub left with no
    /// hub set forgets its `near` names, and their needs. In O(log n) for each hub and pair of
    /// hubs, and for each `near` name of such a hub as [`Conjuncts::contribute`] costs.
    fn close(&mut self, hs: &Hubs, log: &mut Moves) {
        self.index.refused.remove(hs);
        for h in hs.iter() {
            let a = &mut self.index.admit;
            if let Some(k) = a.hits.remove(&(h.clone(), hs.clone())) {
                a.level.remove(h, &(k, hs.clone()));
            }
            for z in hs.iter().filter(|z| *z != h) {
                let key = (h.clone(), z.clone());
                if let Some(s) = a.pair.get_mut(&key) {
                    s.remove(hs);
                    if s.is_empty() {
                        a.pair.remove(&key);
                    }
                }
            }
            if a.level.count(h) == 0 {
                if let Some(near) = self.index.near.remove(h) {
                    for y in near.keys() {
                        self.index.nearby.remove(y, h);
                        self.contribute(h, y, false, log);
                    }
                }
                let needs = self.index.admit.needs.remove(h);
                debug_assert!(needs.is_none_or(|m| m.is_empty()), "needs left at {h}");
            }
        }
    }

    /// Counts hub `h`'s `near` names and their `needs` from its free conjuncts as last found,
    /// when it has none yet. In O(log n) for each name of each free conjunct at `h`, and as
    /// [`Conjuncts::contribute`] costs for each.
    fn view(&mut self, h: &Arc<str>, log: &mut Moves) {
        if self.index.near.contains_key(h) {
            return;
        }
        let mut near: OrdMap<Arc<str>, usize> = OrdMap::new();
        for g in self.index.free.of(h) {
            for y in names(g).into_iter().filter(|y| y != h) {
                *near.entry(y).or_default() += 1;
            }
        }
        self.index.admit.needs.insert(h.clone(), OrdMap::new());
        for y in near.keys() {
            self.index.nearby.add(y, h);
            self.contribute(h, y, true, log);
        }
        self.index.near.insert(h.clone(), near);
    }

    /// Counts in (`up`) or out the needs of `y` as a `near` name of hub `h`, `h` already put
    /// in or taken out of `nearby` ([`Admit::needs`]): of a satellite, a name of no free
    /// conjunct of other than two names, as [`StarIndex::place`] counts them; of any other
    /// name, itself. In O(log n); and for a satellite with no anchor, or whose anchor comes or
    /// goes, as `place` costs.
    fn contribute(&mut self, h: &Arc<str>, y: &Arc<str>, up: bool, log: &mut Moves) {
        let x = &mut *self.index;
        if x.wide.contains_key(y) {
            x.admit.need(h, y, up, log);
            return;
        }
        match x.anchor.get(y) {
            Some(a) if a == h => {
                // `h` leaves: its own needs go, then the others need a new anchor.
                for z in x.ties.get(y).into_iter().flat_map(OrdMap::keys) {
                    if z != h {
                        x.admit.need(h, z, false, log);
                    }
                }
                x.reanchor(y, log);
            }
            Some(a) => x.admit.need(h, a, up, log),
            None => {
                for z in x.ties.get(y).into_iter().flat_map(OrdMap::keys) {
                    if z != h {
                        x.admit.need(h, z, up, log);
                    }
                }
                if up && x.ties.get(y).is_some_and(|t| t.contains_key(h)) {
                    x.reanchor(y, log);
                }
            }
        }
    }

    /// Counts the free conjunct of names `ns` in (`up`) or out at `y`, one of them, in its
    /// `ties` or `wide`; the needs of `y` at each hub it is near move with them
    /// ([`StarIndex::place`]). In O(log n) when `y` has an anchor that stays; for a satellite
    /// with none, O(log n) for each hub it is near; and when its anchor comes or goes, or `y`
    /// becomes a satellite or stops being one, as `place` costs.
    fn tie(&mut self, y: &Arc<str>, ns: &BTreeSet<Arc<str>>, up: bool, log: &mut Moves) {
        let x = &mut *self.index;
        let step = |c: usize| if up { c + 1 } else { c - 1 };
        if ns.len() == 2 {
            let Some(z) = ns.iter().find(|n| *n != y) else {
                unreachable!("two names, one of them `y`")
            };
            let c = x.ties.get(y).and_then(|t| t.get(z)).copied().unwrap_or(0);
            let moves = c == usize::from(!up) && !x.wide.contains_key(y);
            let anchor = x.anchor.get(y).cloned();
            let gone = moves && anchor.as_ref() == Some(z);
            if gone {
                x.place(y, false, log);
            }
            let t = x.ties.entry(y.clone()).or_default();
            match step(c) {
                0 => {
                    t.remove(z);
                }
                c => {
                    t.insert(z.clone(), c);
                }
            }
            if t.is_empty() {
                x.ties.remove(y);
            }
            if gone {
                x.repick(y, log);
            } else if moves {
                match anchor {
                    Some(a) => x.admit.need(&a, z, up, log),
                    None => {
                        for h in x.nearby.of(y).filter(|h| *h != z) {
                            x.admit.need(h, z, up, log);
                        }
                        if up && x.nearby.has(y, z) {
                            x.reanchor(y, log);
                        }
                    }
                }
            }
            return;
        }
        let w = x.wide.get(y).copied().unwrap_or(0);
        let flips = w == usize::from(!up);
        if flips {
            // `y` stops being a satellite (`up`) or becomes one.
            if up {
                x.place(y, false, log);
                x.anchor.remove(y);
            }
            for h in x.nearby.of(y) {
                x.admit.need(h, y, up, log);
            }
        }
        match step(w) {
            0 => {
                x.wide.remove(y);
            }
            w => {
                x.wide.insert(y.clone(), w);
            }
        }
        if flips && !up {
            x.repick(y, log);
        }
    }

    /// Finds again whether each conjunct `p` names is free at each of its names, and keeps
    /// `ties`, `wide`, `near` and the needs of each hub with it ([`Admit`]): the leaves of the
    /// hub sets whose hubs come to admit them all, or no longer do, are put in `check`. In
    /// O(log n) for each conjunct and name of it, and as [`Conjuncts::tie`] and
    /// [`Conjuncts::contribute`] cost; for each hub of hub sets among them, O(log n) for each
    /// other name; for each need a hub gains or loses, O(log n) for each hub set at the hub
    /// that holds it; for each hub whose number of needs changes, its hub sets that it
    /// admitted or admits; and the leaves of the hub sets that come to be admitted or stop.
    fn refree(&mut self, p: &mut Pending, check: &mut BTreeSet<Arc<str>>) {
        let mut log = std::mem::take(&mut p.moves);
        for g in std::mem::take(&mut p.free) {
            let ns = names(&g);
            // Complexity tradeoff: naive version, `users` was asked at each name of `g`
            // whether it holds `g`, each lookup comparing `g` whole with the conjuncts at the
            // name: O(s²) for a disjunction of s atoms that has just left the relation while
            // its join, which begins with it, came in. Used: `users` holds at each name of a
            // conjunct exactly the conjuncts of the set ([`Conjuncts::and_one`],
            // [`Conjuncts::unindex`]), so one lookup in the set answers for every name, O(s)
            // for the comparison; the same answers. COMPLEXITY.md C51.
            let held = self.set.contains(&g);
            for h in &ns {
                let want = held && !self.index.owned.has(h, &g) && !self.index.solo.has(h, &g);
                if want == self.index.free.has(h, &g) {
                    continue;
                }
                if want {
                    self.index.free.add_with(h, &g, &mut self.last);
                } else {
                    self.index.free.remove_with(h, &g, &mut self.last);
                }
                Rows::change(&mut self.index.free_rows, h, &g, want);
                self.tie(h, &ns, want, &mut log);
                for y in ns.iter().filter(|y| *y != h) {
                    let Some(near) = self.index.near.get_mut(h) else {
                        break;
                    };
                    let c = near.get(y).copied().unwrap_or(0);
                    match (want, c) {
                        (true, _) => {
                            near.insert(y.clone(), c + 1);
                        }
                        (false, 1) => {
                            near.remove(y);
                        }
                        (false, _) => {
                            near.insert(y.clone(), c - 1);
                        }
                    }
                    if c != usize::from(!want) {
                        continue;
                    }
                    if want {
                        self.index.nearby.add(y, h);
                    } else {
                        self.index.nearby.remove(y, h);
                    }
                    self.contribute(h, y, want, &mut log);
                }
            }
        }
        self.readmit(&log, check);
    }

    /// Puts in `check` the leaves of each hub set whose hubs came to admit it all, or no
    /// longer do, by the moves `log` recorded: a hub admits a hub set when the set holds all
    /// its needs, so only a hub set whose hits moved, or whose hits equal the old or the new
    /// number of needs of a hub whose number moved, may change. A hub set opened in the change
    /// is counted afresh, its leaves already in `check`; one closed in it is gone. In O(log n)
    /// for each such hub set and each hub of one opened, and the leaves of those that change.
    fn readmit(&mut self, log: &Moves, check: &mut BTreeSet<Arc<str>>) {
        let StarIndex {
            admit,
            refused,
            sets,
            ..
        } = &mut *self.index;
        let len = |h: &str| admit.needs.get(h).map_or(0, OrdMap::len);
        let mut seen: BTreeSet<(Arc<str>, Hubs)> = log.hits.keys().cloned().collect();
        for (h, &before) in &log.lens {
            let after = len(h);
            if after != before {
                for k in [before, after] {
                    let at = admit.level.within(h, k..=k);
                    seen.extend(at.into_iter().map(|hs| (h.clone(), hs)));
                }
            }
        }
        // Whether each hub set whose hubs' admissions moved was admitted by them all before.
        let mut was: BTreeMap<Hubs, bool> = BTreeMap::new();
        for key in seen.into_iter().filter(|(_, hs)| !log.fresh.contains(hs)) {
            let Some(&k) = admit.hits.get(&key) else {
                continue;
            };
            let k0 = log.hits.get(&key).copied().unwrap_or(k);
            let n = len(&key.0);
            let n0 = log.lens.get(&key.0).copied().unwrap_or(n);
            let (then, now) = (k0 == n0, k == n);
            if then == now {
                continue;
            }
            let Some(r) = refused.get_mut(&key.1) else {
                unreachable!("each hub set at a hub is counted")
            };
            was.entry(key.1).or_insert(*r == 0);
            if now {
                *r -= 1;
            } else {
                *r += 1;
            }
        }
        for hs in &log.fresh {
            if let Some(r) = refused.get_mut(hs) {
                *r = hs
                    .iter()
                    .filter(|h| admit.hits[&((*h).clone(), hs.clone())] != len(h))
                    .count();
            }
        }
        for (hs, then) in was {
            if (refused.get(&hs) == Some(&0)) != then {
                check.extend(sets.get(&hs).into_iter().flatten().cloned());
            }
        }
    }

    /// Notes that `g` came to (`added`) or left each of the names `ns`, whose counts are
    /// already changed: the names whose shape that may change are put in `p`. A name of no
    /// shape stays so as long as what its `Why` names stands, which costs O(log n) here: so a
    /// hub of many conjuncts is not looked at again for each conjunct that comes.
    fn counted(&mut self, g: &Arc<Formula>, ns: &BTreeSet<Arc<str>>, added: bool, p: &mut Pending) {
        p.free.insert(g.clone());
        for n in ns {
            let count = self.users.count(n);
            let Some(w) = self.index.whys.get(n).cloned() else {
                p.eval.insert(n.clone());
                continue;
            };
            let witness = w.count.as_ref().filter(|h| self.users.count(h) <= count);
            if !added && (w.by.contains(g) || (w.count.is_some() && witness.is_none())) {
                p.eval.insert(n.clone());
                continue;
            }
            if let Some(h) = &w.count {
                self.index.witnessed.remove(h, &(w.size, n.clone()));
                self.index.witnessed.add(h, &(count, n.clone()));
            }
            self.index.whys.insert(
                n.clone(),
                Arc::new(Why {
                    size: count,
                    ..Why::clone(&w)
                }),
            );
        }
        // A name `n` witnessed against that now has fewer conjuncts than `n`, and a leaf at a
        // hub `n` that now has no fewer than it.
        for n in ns {
            let count = self.users.count(n);
            let found = if added {
                self.index.witnessed.within(n, ..count)
            } else {
                self.index.shaped.within(n, count..)
            };
            p.eval.extend(found);
        }
    }

    /// Finds the shapes `p` names again; then the stars of the names whose shape changed or
    /// that a hub came to admit or no longer admits ([`Conjuncts::refree`]); then places each
    /// conjunct added and not yet in a block, in the forest in place of the one it replaces
    /// when it can.
    fn flush(&mut self, mut p: Pending) {
        if self.is_bottom() {
            return;
        }
        let mut check = std::mem::take(&mut p.eval);
        for x in &check {
            self.unshape(x, &mut p);
        }
        for x in &check {
            self.reshape(x, &mut p);
        }
        self.refree(&mut p, &mut check);
        // The stars that go or change first, so that a conjunct moving from one leaf's star to
        // another's is out of its block when the second takes it.
        let mut loose: Vec<Arc<Formula>> = Vec::new();
        let mut new: Vec<(Arc<str>, Arc<Shape>)> = Vec::new();
        for x in &check {
            let shape = self
                .index
                .shapes
                .get(x)
                .filter(|s| s.hubs.len() == 1 || self.index.refused.get(&s.hubs) == Some(&0));
            let old = self.index.stars.get(x).copied();
            if let (Some(b), Some(s)) = (old, shape)
                && self.blocks.members(b).eq(s.gs.iter())
            {
                continue;
            }
            if let Some(s) = shape {
                new.push((x.clone(), s.clone()));
            }
            if let Some(b) = old {
                self.index.stars.remove(x);
                self.unclass(x);
                let gs: Vec<Arc<Formula>> = self.blocks.members(b).cloned().collect();
                self.blocks.undetach(b);
                for g in &gs {
                    for h in names(g).into_iter().filter(|h| h != x) {
                        self.blocks.hang(&h, g, false);
                        if self.users.has(&h, g) {
                            self.index.moving.add(&h, g);
                        }
                    }
                }
                loose.extend(gs);
            }
        }
        for (x, s) in new {
            let forest: Vec<Arc<Formula>> =
                s.gs.iter()
                    .filter(|g| self.blocks.placed(g))
                    .cloned()
                    .collect();
            if !forest.is_empty() {
                self.blocks.remove(&forest);
            }
            let b = self.blocks.detach(s.gs.iter().cloned());
            self.index.stars.insert(x.clone(), b);
            self.enclass(&x, &s.gs, &s.hubs);
            for g in &s.gs {
                for h in names(g).into_iter().filter(|h| *h != x) {
                    self.blocks.hang(&h, g, true);
                    self.index.moving.remove(&h, g);
                }
            }
        }
        for g in loose {
            if self.set.contains(&g) && self.blocks.of(&g).is_none() {
                self.blocks.add(&g);
            }
        }
        let mut drop: BTreeSet<Arc<Formula>> = BTreeSet::new();
        for (g, old) in p.placed {
            let old = old.filter(|o| !self.set.contains(o) && self.blocks.placed(o));
            if self.set.contains(&g) && self.blocks.of(&g).is_none() {
                match old {
                    Some(o) if !drop.contains(&o) => self.blocks.replace(&o, &g),
                    _ => self.blocks.add(&g),
                }
            } else if let Some(o) = old {
                drop.insert(o);
            }
        }
        if !drop.is_empty() {
            let drop: Vec<Arc<Formula>> = drop.into_iter().collect();
            self.blocks.remove(&drop);
        }
    }

    /// The conjunction as one formula, as [`Formula::and`] gives it.
    pub fn formula(&self) -> Formula {
        let mut gs: Vec<Formula> = self.set.iter().map(|g| (**g).clone()).collect();
        if gs.len() == 1 {
            gs.pop().expect("one")
        } else {
            Formula::And(Shared::new(gs))
        }
    }

    /// Each constraint, conjunct by conjunct.
    pub fn cons(&self) -> Vec<&Con> {
        self.set.iter().flat_map(|g| g.cons()).collect()
    }

    /// The conjunction with `f`: a conjunction's parts are added each, `true` is dropped and
    /// `false` absorbs, and of two constraints on one term with one relation the tighter
    /// alone is kept, as [`Formula::and`] does; of two disjunctions of two constraints on one
    /// pair of terms, one implied by the other goes. A conjunct of no atoms, such as the
    /// `!(0 == 0)` of a test `x != x`, is decided at once: it is `true` or `false`, since no
    /// block holds it and no projection would read it.
    pub fn and(&mut self, f: Formula) {
        let mut held = Held::new();
        let mut p = Pending::default();
        self.and_held(f, &mut held, &mut p);
        self.flush(p);
        // The disjunctions a stronger one replaced and no conjunct took the place of
        // ([`Conjuncts::pair`]).
        let rest: Vec<Arc<Formula>> = held.into_values().flatten().collect();
        self.unplace(&rest);
    }

    /// The conjunction without the conjuncts `gone` and with `f`, in time near theirs: a
    /// conjunct of `f` of the same atoms as one of `gone` takes its place in its block
    /// ([`Blocks::replace`]), and the others of `gone` leave the blocks before the conjuncts of
    /// `f` are placed. So the join of two cases that differ in a conjunct of a chain replaces
    /// it, where removing it first would cut the chain and build the blocks of the rest again.
    pub fn swap(&mut self, gone: &[Arc<Formula>], f: Formula) {
        let mut held = Held::new();
        let mut p = Pending::default();
        for g in gone {
            if self.unindex(g, &mut p) {
                held.entry(g.atoms()).or_default().push(g.clone());
            }
        }
        self.and_held(f, &mut held, &mut p);
        // Complexity tradeoff: naive version, the conjuncts of `f` were placed while those of
        // `gone` that none replaces were still in the blocks, and these left afterward. A join
        // gives one disjunction `D || D'` in place of `D` ([`Formula::either`]), whose parts
        // begin with D's, so each of its s names put it beside D in the blocks' sets of
        // conjuncts by name (`syms`, `at`), each insertion and the removal of D comparing the
        // two through D's length: O(s²) a join, and quadratic in all for a nest of k excluded
        // sides (s near k). Used: those of `gone` leave first, so D and its join are never in
        // one set: O(s log s) a join. The blocks are those of the same conjuncts, a function of
        // the set alone. COMPLEXITY.md C51.
        let rest: Vec<Arc<Formula>> = held.into_values().flatten().collect();
        self.unplace(&rest);
        self.flush(p);
    }

    /// Adds the conjuncts of `f`, read on an explicit stack in order. A conjunction held in
    /// more than one place (a named conjunction that `Formula::and` keeps whole, used inside
    /// another) is read once, at its first place: a conjunct added twice changes nothing, and
    /// a chain of names each conjoining the two before it would otherwise be read once for
    /// each path to it, a number exponential in its length.
    fn and_held(&mut self, f: Formula, held: &mut Held, p: &mut Pending) {
        // The conjunctions read, by id: a copy of one read before is passed over even when the
        // copies read are gone and it is the last holder.
        let mut seen: HashSet<Id> = HashSet::new();
        let mut stack = vec![f];
        while let Some(g) = stack.pop() {
            let Formula::And(gs) = &g else {
                self.and_one(g, held, p);
                continue;
            };
            if !seen.insert(Id::any(&g)) {
                continue;
            }
            if Shared::strong_count(gs) == 1 {
                stack.extend(g.into_parts().expect("a conjunction").into_iter().rev());
            } else {
                stack.extend(gs.iter().rev().cloned());
            }
        }
    }

    fn and_one(&mut self, g: Formula, held: &mut Held, p: &mut Pending) {
        if self.is_bottom() {
            return;
        }
        match &g {
            Formula::Or(gs) if gs.is_empty() => {
                *self = Conjuncts::default();
                self.set.insert(Arc::new(g));
                held.clear();
                return;
            }
            Formula::And(_) => return self.and_held(g, held, p),
            _ => {}
        }
        // `!(t >= 0)` is the constraint `-t - 1 >= 0` on the integers, which is projected with
        // every part of its block ([`Formula::cons`]), where its negation would be a part alone.
        let g = match &g {
            Formula::Not(n) => match &**n {
                Formula::Con(c) if c.rel == Rel::Ge => Formula::Con(Con {
                    lin: Lin::constant(-1).minus(&c.lin),
                    rel: Rel::Ge,
                }),
                _ => g,
            },
            _ => g,
        };
        if g.atoms().is_empty() {
            if !g.holds(&Model::new()) {
                self.and_one(Formula::bottom(), held, p);
            }
            return;
        }
        // The looser constraint on the same term, which `g` replaces in its block.
        // Complexity tradeoff: looked up by a borrow of the constraint's own term, where the key
        // `(term, rel)` cloned the term first, O(t) a lookup; now O(t log m) for the comparisons
        // alone, for m constraints kept. COMPLEXITY.md C46.
        let mut looser = None;
        if let Formula::Con(c) = &g
            && let Some(old) = self.tight[tight_at(c.rel)].get(&c.lin.terms)
        {
            let Formula::Con(o) = &**old else {
                unreachable!("a constraint")
            };
            if c.rel == Rel::Ge && c.lin.constant < o.lin.constant {
                let old = old.clone();
                self.unindex(&old, p);
                looser = Some(old);
            } else if c.rel == Rel::Eq && c.lin.constant != o.lin.constant {
                self.and_one(Formula::bottom(), held, p);
                return;
            } else {
                return;
            }
        }
        let g = Arc::new(g);
        if self.set.contains(&g) {
            return;
        }
        if !self.pair(&g, held, p) {
            return;
        }
        let ns = names(&g);
        let is_eq = matches!(&*g, Formula::Con(c) if c.rel == Rel::Eq);
        for n in &ns {
            self.users.add_with(n, &g, &mut self.last);
            self.index.moving.add_with(n, &g, &mut self.last);
            if is_eq {
                self.eq_users.add(n, &g);
            }
        }
        if let Some(n) = alone(&g) {
            self.index.solo.add(&n, &g);
        }
        if let Formula::Con(c) = &*g {
            // Complexity tradeoff: the one copy of the term, made once per constraint kept and
            // shared by every later path copy, O(t) once. COMPLEXITY.md C46.
            self.tight[tight_at(c.rel)].insert(Arc::new(c.lin.terms.clone()), g.clone());
        }
        // Else a conjunct of the same atoms [`Conjuncts::swap`] removes, `g` itself first.
        let old = looser.or_else(|| {
            let same = held.get_mut(&g.atoms())?;
            let i = same
                .iter()
                .position(|h| *h == g)
                .or(same.len().checked_sub(1))?;
            Some(same.swap_remove(i))
        });
        self.set.insert(g.clone());
        self.counted(&g, &ns, true, p);
        p.placed.push((g, old));
    }

    /// The rule that keeps the stronger of two disjunctions of two constraints on one pair of
    /// terms, as the tighter of two constraints on one term is kept: whether `g`, new, is to be
    /// added. `f + c >= 0 || g + d >= 0` implies `f + c' >= 0 || g + d' >= 0` when `c <= c'`
    /// and `d <= d'`, so of the disjunctions on one pair of terms only those that no other
    /// implies are kept, the maximal ones (a Pareto front). Each one `g` implies leaves every
    /// index but the blocks, where `g` takes its place ([`Held`], [`Conjuncts::and`]). The
    /// conjuncts kept depend on the set added alone, not on its order; a scope's disjunctions
    /// on two forms, as the bounds `x + y >= j || x - y >= j` of COMPLEXITY.md C26, are then as
    /// many as the incomparable ones and not one per test. In O(log n) for each disjunction
    /// added, and O(log n) for each one it removes, which was added once.
    fn pair(&mut self, g: &Arc<Formula>, held: &mut Held, p: &mut Pending) -> bool {
        let Some((key, c, d)) = pair_of(g) else {
            return true;
        };
        let front = self.pairs.get(&key).cloned().unwrap_or_default();
        // The kept disjunction with the greatest first constant at most `c` has the least
        // second constant of those, so `g` is implied when that one's is at most `d`.
        if front
            .range(..=c.clone())
            .next_back()
            .is_some_and(|(_, (d2, _))| *d2 <= d)
        {
            return false;
        }
        // Those `g` implies: from first constant `c` up, while the second is at least `d`.
        let implied: Vec<Arc<Formula>> = front
            .range(c.clone()..)
            .take_while(|(_, (d2, _))| *d2 >= d)
            .map(|(_, (_, h))| h.clone())
            .collect();
        for h in implied {
            if self.unindex(&h, p) {
                held.entry(h.atoms()).or_default().push(h);
            }
        }
        // Complexity tradeoff: the key is put behind an `Arc` only when it is new, one
        // allocation, so that later path copies share it. COMPLEXITY.md C46.
        match self.pairs.get_mut(&key) {
            Some(front) => {
                front.insert(c, (d, g.clone()));
            }
            None => {
                self.pairs
                    .insert(Arc::new(key), OrdMap::unit(c, (d, g.clone())));
            }
        }
        true
    }

    /// Removes `g` from the set and from every index but the blocks; whether it was there.
    /// A star that held it is changed by [`Conjuncts::flush`].
    fn unindex(&mut self, g: &Arc<Formula>, p: &mut Pending) -> bool {
        if self.set.remove(g).is_none() {
            return false;
        }
        let ns = names(g);
        let is_eq = matches!(&**g, Formula::Con(c) if c.rel == Rel::Eq);
        for n in &ns {
            self.users.remove_with(n, g, &mut self.last);
            self.index.moving.remove_with(n, g, &mut self.last);
            if is_eq {
                self.eq_users.remove(n, g);
            }
        }
        if let Some(n) = alone(g) {
            self.index.solo.remove(&n, g);
        }
        self.counted(g, &ns, false, p);
        if let Formula::Con(c) = &**g {
            // Complexity tradeoff: looked up and removed by a borrow of the term, where the key
            // `(term, rel)` cloned the term first, O(t); the path copy of the removal clones
            // each key of a node in O(1). COMPLEXITY.md C46.
            let tight = &mut self.tight[tight_at(c.rel)];
            if tight.get(&c.lin.terms) == Some(g) {
                tight.remove(&c.lin.terms);
            }
        }
        if let Some((key, c, _)) = pair_of(g)
            && let Some(front) = self.pairs.get_mut(&key)
            && front.get(&c).is_some_and(|(_, h)| h == g)
        {
            front.remove(&c);
            if front.is_empty() {
                self.pairs.remove(&key);
            }
        }
        true
    }

    /// Takes the conjuncts `gs`, already out of the set, out of the forest, those in it.
    fn unplace(&mut self, gs: &[Arc<Formula>]) {
        let forest: Vec<Arc<Formula>> = gs
            .iter()
            .filter(|g| self.blocks.placed(g))
            .cloned()
            .collect();
        if !forest.is_empty() && !self.is_bottom() {
            self.blocks.remove(&forest);
        }
    }

    /// Removes the conjunct `g`.
    pub fn remove(&mut self, g: &Arc<Formula>) {
        let mut p = Pending::default();
        if self.unindex(g, &mut p) {
            self.flush(p);
            self.unplace(std::slice::from_ref(g));
        }
    }

    /// The conjunction with every conjunct that mentions `name` replaced by
    /// [`Formula::forget`] of it, which says nothing of `name`: in time near the conjuncts
    /// that mention it, but for the blocks, which are built again over the conjuncts linked
    /// to them when one is not a leaf of its tree ([`Blocks::remove`]).
    pub fn forget(&mut self, name: &Arc<str>) {
        let gs: Vec<Arc<Formula>> = self.mentioning(name).cloned().collect();
        let mut p = Pending::default();
        for g in &gs {
            self.unindex(g, &mut p);
        }
        self.flush(p);
        self.unplace(&gs);
        let mut held = Held::new();
        let mut p = Pending::default();
        for g in gs {
            self.and_held(g.forget(name), &mut held, &mut p);
        }
        self.flush(p);
        let rest: Vec<Arc<Formula>> = held.into_values().flatten().collect();
        self.unplace(&rest);
    }
}

/// The equality constraints (`Rel::Eq`) of `rels` linked to `seeds` by chains of equalities
/// that share a name, and the names they mention with the seeds: a search with a visited set
/// over `Conjuncts::eq_users`, in time near the equalities found (O(seeds) when none exist).
pub fn reach_eqs(
    rels: &[&Conjuncts],
    seeds: impl IntoIterator<Item = Arc<str>>,
) -> (BTreeSet<Arc<Formula>>, BTreeSet<Arc<str>>) {
    linked(rels, seeds, |r| &r.eq_users, |_| true)
}

/// The conjuncts of `rels` linked to `seeds` by chains of conjuncts that share a name, only
/// conjuncts `follow` keeps taken, and the names they mention with the seeds: a search from
/// the seeds with a visited set, in time near the conjuncts found.
pub fn reach(
    rels: &[&Conjuncts],
    seeds: impl IntoIterator<Item = Arc<str>>,
    follow: impl Fn(&Formula) -> bool,
) -> (BTreeSet<Arc<Formula>>, BTreeSet<Arc<str>>) {
    linked(rels, seeds, |r| &r.users, follow)
}

/// The search of [`reach`] and [`reach_eqs`] ([`zed_graph::reach`] over the names, the
/// visited set `seen`): from each name to the conjuncts `uses` files under it that `follow`
/// keeps and that are not yet `found`, and on to the names they mention.
fn linked<'r>(
    rels: &[&'r Conjuncts],
    seeds: impl IntoIterator<Item = Arc<str>>,
    uses: impl Fn(&'r Conjuncts) -> &'r Uses<Arc<Formula>>,
    follow: impl Fn(&Formula) -> bool,
) -> (BTreeSet<Arc<Formula>>, BTreeSet<Arc<str>>) {
    let mut found: BTreeSet<Arc<Formula>> = BTreeSet::new();
    let mut seen: BTreeSet<Arc<str>> = BTreeSet::new();
    zed_graph::reach(
        seeds,
        |n| seen.insert(n.clone()),
        |n| {
            let mut next = Vec::new();
            for g in rels.iter().flat_map(|r| uses(r).of(n)) {
                if follow(g) && found.insert(g.clone()) {
                    next.extend(names(g));
                }
            }
            next
        },
    );
    (found, seen)
}

/// A block of a [`Blocks`] forest, or a name in it.
pub type BlockId = u64;

/// A node in the persistent union-find over merged-away block ids ([`Blocks::uf`]):
/// unmerged blocks and name ids are absent (implicitly `Root { rank: 0, live: id }`).
#[derive(Clone, Copy, Debug)]
enum UfNode {
    /// Merged into `parent`.
    Parent(BlockId),
    /// Root of a merged group with union-by-rank `rank` and live block id `live`.
    Root { rank: u8, live: BlockId },
}

/// Ascending live block ids for [`Blocks::moving_blocks`]: zero-allocation for 0 or 1 block.
enum MovingBlocks {
    Empty,
    One(Option<BlockId>),
    Many(std::vec::IntoIter<BlockId>),
}

impl Iterator for MovingBlocks {
    type Item = BlockId;

    fn next(&mut self) -> Option<BlockId> {
        match self {
            MovingBlocks::Empty => None,
            MovingBlocks::One(b) => b.take(),
            MovingBlocks::Many(it) => it.next(),
        }
    }
}

/// The blocks of a conjunction, kept as conjuncts are added and removed, and the forest they
/// form with the names. Conjuncts that share an atom other than a name are in one block; the
/// blocks are then the biconnected components of the graph whose vertices are these groups and
/// the names, with an edge from a group to each name it mentions, where components that share
/// a group are one block. Two blocks share at most one name, and blocks and names form a
/// forest, each tree rooted somewhere and held by parent links, each node labeled with its
/// tree; when two trees join, the smaller one's nodes are labeled again.
///
/// A new conjunct is a block of its own: it is linked to each tree of a name it mentions that
/// is not yet its own, by rerooting the smaller tree (so a node is rerooted O(log n) times),
/// and when it meets its own tree a second time, the blocks on the tree path between are
/// merged into one, keeping the largest block (`Blocks::merge`). Block-local indexes (`members`,
/// `names_in`, `at`, `pairs`) merge via join-based B+Tree union in O(W log W) total across all
/// merges, and merged-away block ids in `of`, `up`, and private `moving_at` entries resolve
/// lazily through the persistent union-find `uf`. A removed conjunct of two names and no other
/// atom is taken out in time near the smaller side of each split it makes, searched from both
/// of its names in turn (`Blocks::cut`). Any other removed conjunct that is a block alone and
/// shares at most one name with the rest is unlinked in O(log n); a removal from a block of
/// names whose other conjuncts still link all its names places those conjuncts again, in time
/// near the block (`Blocks::split`); any other removal rebuilds the blocks of the conjuncts
/// linked to it, in time near their number. The blocks do not depend on the order the conjuncts
/// came in; the roots and the numbers do, and nothing reads them but this forest.
#[derive(Clone, Debug, Default)]
pub struct Blocks {
    /// The next number for a block or a name.
    next: BlockId,
    /// Each name's number.
    name: OrdMap<Arc<str>, BlockId>,
    /// Each conjunct's block (possibly a merged-away id resolved through [`Blocks::uf`]).
    // Complexity tradeoff: naive version, an `OrdMap` keyed by the formula, O(log n)
    // comparisons a lookup, each a walk of two constraints' terms (about 220 instructions):
    // near 2,400 instructions a lookup at 2,000 conjuncts, and growing with log n, which made
    // the chain raise in reverse 9.57 times at 8n (`xst::s4`). Used: a persistent hash map
    // (Bagwell's hash array mapped trie: P. Bagwell, "Ideal Hash Trees", EPFL technical
    // report, 2001, no DOI found on Crossref, not read; imbl `GenericHashMap`), one hash of
    // the formula (`Formula`'s `Hash`, kept with a compound node, linear in a constraint's
    // size) and one comparison, which a key held at the same address answers by its
    // pointer, so O(1) expected a lookup; merged-away block ids are resolved lazily through
    // `uf`, avoiding rewriting `of` for every moved conjunct during `Blocks::merge`. This map
    // is only read
    // by key, never in order, so no order is lost; its hasher is the seeded `TextState` over
    // the formula's own hash, since a formula holds a program's names (it was `FxBuildHasher`,
    // with no seed; DRY-sorted-structures-2 job 3). Test
    // `l01_39_scope_relations::xst::s4::a_chain_raise_in_reverse_narrows_in_near_linear_time`;
    // COMPLEXITY.md row ST-chain-raise-reverse-log, PERF-satellite-random-under9-redesign.
    of: GenericHashMap<Arc<Formula>, BlockId, TextState, DefaultSharedPtr>,
    /// Persistent union-find over merged-away block ids (union by rank with root live id;
    /// path compression on `&mut self` reads): resolves stale block ids stored in `of`, `up`,
    /// and `moving_at` in `O(1)` when unmerged and `<= log₂ n` HAMT hops worst-case
    /// (`O(alpha(n) log_{32} n)` amortized on linear histories, Tarjan 1975).
    // Complexity tradeoff: naive version, `Blocks::merge` rewrote `of` for every moved
    // conjunct (`O(n log n * log_{32} n)`), `up` for every child name (`O(W log^2 n)`), and
    // `moving_at` for every name of the merged-away block (`O(W log^2 n)`), because their
    // outer keys are not `BlockId`. Used: record `b -> keep` in `uf` in `O(log_{32} n)` per
    // merged-away block (`O(n log n)` total across all merges) and resolve lazily on reads.
    // Tradeoff: readers of merged blocks pay `uf` resolution hops (`<= log₂ n` worst-case on
    // branched immutable reads; `O(alpha(n))` amortized on linear `&mut self` walks).
    // Tarjan, JACM 22(2), 1975. COMPLEXITY.md row PERF-satellite-random-under9-redesign.
    // Keyed by block numbers the compiler drew, so the unseeded `Digest`.
    uf: GenericHashMap<BlockId, UfNode, std::hash::BuildHasherDefault<Digest>, DefaultSharedPtr>,
    /// Each block's conjuncts.
    members: OrdMap<BlockId, OrdSet<Arc<Formula>>>,
    /// Each node's parent in its tree (a name's parent block may be a merged-away id resolved
    /// through [`Blocks::uf`]); a root has none.
    up: OrdMap<BlockId, BlockId>,
    /// The tree of each node of the forest: a number of its own, never a node's.
    tree_of: OrdMap<BlockId, BlockId>,
    /// The nodes of each tree.
    trees: OrdMap<BlockId, OrdSet<BlockId>>,
    /// The conjuncts that mention each name as an atom of its own.
    syms: Uses<Arc<Formula>>,
    /// For each block, its conjuncts that mention each name as an atom of its own, the entries
    /// of `syms` cut by `of`; none empty.
    // Complexity tradeoff: naive version, a flat `OrdMap<(Arc<str>, BlockId), OrdSet<...>>`
    // required one outer `O(log n)` remove + insert per name of a merged-away block in
    // `Blocks::merge`, `O(W log^2 n)` over balanced merges. Used: nested by `BlockId` first
    // (`OrdMap<BlockId, OrdMap<Arc<str>, OrdSet<Arc<Formula>>>>`) so `Blocks::merge` removes
    // a block's whole inner map and merges it with join-based `OrdMap::union_with` +
    // `OrdSet::union` (Blelloch, Ferizovic and Sun, SPAA 2016, doi:10.1145/2935764.2935768;
    // Brown and Tarjan, JACM 1979, doi:10.1145/322123.322127), `O(W log W)` total over all
    // merges, while `Blocks::advance` still looks up `(b, x)` in `O(log n)`. COMPLEXITY.md
    // row PERF-satellite-random-under9-redesign.
    at: OrdMap<BlockId, OrdMap<Arc<str>, OrdSet<Arc<Formula>>>>,
    /// The conjuncts of the forest's blocks, not those apart from it, that mention each name
    /// as an atom of its own: the entries of `syms` whose block is in the forest.
    // Complexity tradeoff: a name's conjuncts in its tree could be read from `syms`, skipping
    // those of blocks apart, O(1) to keep but O(d log n) per read for a name of d conjuncts,
    // so a hub of k stars, each a block apart, read once per projection by shortest paths
    // costs O(k log n) a test and O(k² log n) over k tests (`Scope::bound_pass`). This index
    // gives a name's conjuncts in the forest alone, at O(log n) per name of a conjunct each
    // time it moves into or out of the forest, the order `at` already costs, and one entry
    // per name of each conjunct of the forest. Test
    // `l01_39_reduced_product::scaling::tests_on_the_hubs_of_many_stars_in_an_eager_scope_scale`;
    // COMPLEXITY.md row C49.
    forest: Uses<Arc<Formula>>,
    /// The last change to `syms` and `forest`, which share a name's set while they hold the
    /// same conjuncts there ([`Last`]).
    last: Last<Arc<Formula>>,

    /// The conjuncts that mention each atom that is not a name.
    shared: OrdMap<Atom, OrdSet<Arc<Formula>>>,
    /// The blocks apart from the forest, each its own tree ([`Blocks::detach`]).
    apart: OrdSet<BlockId>,
    /// The number of conjuncts of each tree that are not difference constraints or bounds
    /// ([`edges`]), at its representative; none when zero.
    others: OrdMap<BlockId, usize>,
    /// The names that keep their trees from projection by shortest paths ([`Blocks::gap`]).
    gapped: OrdSet<Arc<str>>,
    /// The number of such names of each tree, at its representative; none when zero.
    gaps: OrdMap<BlockId, usize>,
    /// The conjuncts of the stars at each hub ([`Conjuncts::hanging`]), kept by
    /// [`Blocks::hang`].
    hung: Uses<Arc<Formula>>,
    /// For each name, the number of its moving conjuncts in each block, keyed by the block's
    /// stable tag for that name (the `BlockId` recorded in [`Blocks::names_in`], which resolves
    /// through [`Blocks::uf`] to the live block, with no two tags resolving to one block);
    /// none zero.
    // Complexity tradeoff: naive version, updating `moving_at[n]` for every name `n` of a
    // merged-away block in `Blocks::merge` cost `O(k log n)` per merge and `O(W log^2 n)` over
    // balanced merges. Used: each `(b, n)` in `names_in` keeps its tag `tag_b` in
    // `moving_at[n]`; on merge, private names of `b` leave `moving_at` untouched (resolved
    // lazily via `uf`), and only names present in both `b` and `keep` (found during
    // `names_in`'s join-based `union_with_key`) combine their tags in `moving_at[n]`. Each
    // collision permanently lowers `sum_b |names_in[b]|` by 1, so at most `W` collisions occur
    // across all merges: `O(W log n)` total. `moving_blocks(n)` resolves tags and sorts only
    // when a name has 2+ blocks. COMPLEXITY.md row PERF-satellite-random-under9-redesign.
    moving_at: OrdMap<Arc<str>, OrdMap<BlockId, usize>>,
    /// For each block, each name its conjuncts mention ([`names`]) with `(count, tag)`:
    /// `count > 0` is the number of conjuncts mentioning it and `tag` is this block's key in
    /// `moving_at[n]` (`resolve(tag) == b`).
    // Complexity tradeoff: naive version, a flat `OrdMap<(BlockId, Arc<str>), usize>` cost
    // `O(k log n)` per merge (`O(W log^2 n)` over balanced merges). Used: nested by `BlockId`
    // (`OrdMap<BlockId, OrdMap<Arc<str>, (usize, BlockId)>>`) merged by join-based
    // `OrdMap::union_with_key` (Blelloch, Ferizovic and Sun, SPAA 2016,
    // doi:10.1145/2935764.2935768; Brown and Tarjan, JACM 1979, doi:10.1145/322123.322127),
    // `O(W log W)` total over all merges, while `names_of(b)` reads `b`'s inner map directly
    // in ascending name order. COMPLEXITY.md row PERF-satellite-random-under9-redesign.
    names_in: OrdMap<BlockId, OrdMap<Arc<str>, (usize, BlockId)>>,
    /// For each block, the count of its conjuncts on each ordered pair of names `(u, v)` and
    /// no other atom ([`pair`]); none zero.
    // Complexity tradeoff: naive version, a flat `OrdMap<(BlockId, Arc<str>, Arc<str>), usize>`
    // cost `O(p log n)` per merge (`O(n log^2 n)` over balanced merges). Used: nested by
    // `BlockId` (`OrdMap<BlockId, OrdMap<(Arc<str>, Arc<str>), usize>>`) merged by join-based
    // `OrdMap::union_with` (Blelloch, Ferizovic and Sun, SPAA 2016,
    // doi:10.1145/2935764.2935768; Brown and Tarjan, JACM 1979, doi:10.1145/322123.322127),
    // `O(n log n)` total over all merges; `Blocks::cut` still queries `(b, u, v)`
    // in `O(log n)`. COMPLEXITY.md row PERF-satellite-random-under9-redesign.
    pairs: OrdMap<BlockId, OrdMap<NamePair, usize>>,
}

/// Adds `by` to the count of `r` in `counts`, which holds no zero.
// Complexity tradeoff: naive version, the count read and then written back, two descents of
// O(log n) key comparisons for a count that is kept. Used: one descent that changes the count
// in place, a second only to insert a new count or remove one that reaches zero. The same
// O(log n), half the comparisons for a kept count. COMPLEXITY.md row ST-chain-raise-reverse-log.
fn tally<K: Ord + Clone>(counts: &mut OrdMap<K, usize>, r: K, by: isize) {
    match counts.get_mut(&r) {
        Some(c) => {
            let n = c.checked_add_signed(by);
            debug_assert!(n.is_some(), "a count below zero");
            *c = n.unwrap_or(0);
            if *c == 0 {
                counts.remove(&r);
            }
        }
        None => {
            debug_assert!(by >= 0, "a count below zero");
            if by > 0 {
                counts.insert(r, by.unsigned_abs());
            }
        }
    }
}

impl Blocks {
    /// Resolves a possibly merged-away block id to its live block id without path compression.
    fn resolve(&self, mut id: BlockId) -> BlockId {
        if self.uf.is_empty() {
            return id;
        }
        while let Some(&node) = self.uf.get(&id) {
            match node {
                UfNode::Parent(p) => id = p,
                UfNode::Root { live, .. } => return live,
            }
        }
        id
    }

    /// Follows `uf` with path compression, returning `(root_id, rank, live_id)`.
    fn uf_root_mut(&mut self, id: BlockId) -> (BlockId, u8, BlockId) {
        if self.uf.is_empty() {
            return (id, 0, id);
        }
        let Some(&first) = self.uf.get(&id) else {
            return (id, 0, id);
        };
        let p1 = match first {
            UfNode::Root { rank, live } => return (id, rank, live),
            UfNode::Parent(p) => p,
        };
        let p2 = match self.uf.get(&p1).copied() {
            None => return (p1, 0, p1),
            Some(UfNode::Root { rank, live }) => return (p1, rank, live),
            Some(UfNode::Parent(p)) => p,
        };
        let mut trail = vec![id, p1];
        let mut cur = p2;
        let (root, rank, live) = loop {
            match self.uf.get(&cur).copied() {
                None => break (cur, 0, cur),
                Some(UfNode::Root { rank, live }) => break (cur, rank, live),
                Some(UfNode::Parent(p)) => {
                    trail.push(cur);
                    cur = p;
                }
            }
        };
        for &node in &trail[..trail.len() - 1] {
            self.uf.insert(node, UfNode::Parent(root));
        }
        (root, rank, live)
    }

    /// Resolves `id` to its live block id with path compression on `uf`.
    fn resolve_mut(&mut self, id: BlockId) -> BlockId {
        self.uf_root_mut(id).2
    }

    /// Merges block `b`'s union-find group into `keep`'s group by rank, keeping `live = keep`.
    fn uf_merge(&mut self, b: BlockId, keep: BlockId) {
        let (rb, rank_b, _) = self.uf_root_mut(b);
        let (rk, rank_k, _) = self.uf_root_mut(keep);
        debug_assert_ne!(rb, rk, "merging distinct live blocks");
        match rank_b.cmp(&rank_k) {
            std::cmp::Ordering::Less => {
                self.uf.insert(rb, UfNode::Parent(rk));
            }
            std::cmp::Ordering::Greater => {
                self.uf.insert(rk, UfNode::Parent(rb));
                self.uf.insert(
                    rb,
                    UfNode::Root {
                        rank: rank_b,
                        live: keep,
                    },
                );
            }
            std::cmp::Ordering::Equal => {
                self.uf.insert(rb, UfNode::Parent(rk));
                self.uf.insert(
                    rk,
                    UfNode::Root {
                        rank: rank_k.saturating_add(1),
                        live: keep,
                    },
                );
            }
        }
    }

    /// Parent of node `x` in its tree, resolving any merged-away parent block id through `uf`.
    fn parent(&self, x: BlockId) -> Option<BlockId> {
        self.up.get(&x).map(|&p| self.resolve(p))
    }

    /// Parent of node `x` in its tree, compressing `uf` when `x`'s parent block was merged.
    fn parent_mut(&mut self, x: BlockId) -> Option<BlockId> {
        let raw = self.up.get(&x).copied()?;
        Some(self.resolve_mut(raw))
    }

    /// The block of `g`, compressing `uf` when `g`'s stored block id was merged.
    fn of_mut(&mut self, g: &Arc<Formula>) -> Option<BlockId> {
        let raw = self.of.get(g).copied()?;
        Some(self.resolve_mut(raw))
    }

    /// The block of `g`.
    pub fn of(&self, g: &Arc<Formula>) -> Option<BlockId> {
        self.of.get(g).map(|&b| self.resolve(b))
    }

    /// The conjuncts of block `b`.
    pub fn members(&self, b: BlockId) -> impl Iterator<Item = &Arc<Formula>> {
        self.members.get(&b).into_iter().flatten()
    }

    /// The conjuncts of block `b` as their persistent set ([`Uses::set`]).
    pub fn member_set(&self, b: BlockId) -> Option<&OrdSet<Arc<Formula>>> {
        self.members.get(&b)
    }

    /// The names the conjuncts of block `b` mention ([`names`]), in O(log n) and their number.
    pub fn names_of(&self, b: BlockId) -> impl Iterator<Item = &Arc<str>> {
        self.names_in.get(&b).into_iter().flat_map(|m| m.keys())
    }

    /// The blocks that hold now the conjuncts of block `b` of `old`, an earlier state of
    /// these blocks, that are still here.
    // Complexity tradeoff: naive version, the block of each conjunct of `b` looked up,
    // O(d log n) for a block of d conjuncts, so taking one conjunct out of a block of near k
    // at each of k tests costs O(k² log n) (`Scope::due`). Used: when `b` is still a block,
    // the difference of its conjuncts then and now, whose persistent sets share all but the
    // paths to the changes (`OrdSet::diff` skips shared nodes), so O((c + 1) log n) for c
    // conjuncts moved in or out of `b` since, each already paid for when it moved; a block
    // gone is read whole, as before. Test `l01_39_scope_relations::families::coordkk_scales`;
    // COMPLEXITY.md row PERF-l139-due.
    pub fn now_of(&self, old: &Blocks, b: BlockId) -> BTreeSet<BlockId> {
        let Some(then) = old.member_set(b) else {
            return BTreeSet::new();
        };
        let Some(now) = self.member_set(b) else {
            return then.iter().filter_map(|h| self.of(h)).collect();
        };
        let mut out = BTreeSet::new();
        let mut left = then.len();
        for d in then.diff(now) {
            if let imbl::ordset::DiffItem::Remove(h) = d {
                left -= 1;
                out.extend(self.of(h));
            }
        }
        if left > 0 {
            out.insert(b);
        }
        out
    }

    /// The tree of block `b`: one number for all the blocks of one tree.
    pub fn tree(&self, b: BlockId) -> BlockId {
        self.find(b)
    }

    /// Every block.
    pub fn all(&self) -> impl Iterator<Item = BlockId> + '_ {
        self.members.keys().copied()
    }

    /// Whether block `b` is apart from the forest ([`Blocks::detach`]).
    pub fn is_apart(&self, b: BlockId) -> bool {
        self.apart.contains(&b)
    }

    /// Whether `g` is in a block of the forest, not one apart from it
    /// ([`Blocks::detach`]).
    pub fn placed(&self, g: &Arc<Formula>) -> bool {
        self.of(g).is_some_and(|b| !self.is_apart(b))
    }

    /// The conjuncts of the forest, not of a block apart from it, that mention `name` as an
    /// atom of its own, in O(log n) and their number.
    pub fn in_forest(&self, name: &str) -> impl Iterator<Item = &Arc<Formula>> {
        self.forest.of(name)
    }

    /// The tree of the forest that holds `name`, if a conjunct of the forest mentions it.
    pub fn tree_of_name(&self, name: &str) -> Option<BlockId> {
        self.name.get(name).map(|&id| self.find(id))
    }

    /// Whether the tree `t` of the forest holds only difference constraints and bounds
    /// ([`edges`]) and none of its names keeps it from shortest paths ([`Blocks::gap`]): read from
    /// two counts kept as conjuncts come and go, in O(log n).
    pub fn differences_only(&self, t: BlockId) -> bool {
        let r = self.find(t);
        !self.is_apart(r) && !self.others.contains_key(&r) && !self.gaps.contains_key(&r)
    }

    /// The number of names of tree `t` of the forest that keep it from shortest paths
    /// ([`Blocks::gap`])
    /// when it holds only difference constraints and bounds ([`edges`]), otherwise `None`; in
    /// O(log n). [`Blocks::differences_only`] is a count of 0.
    pub fn gaps(&self, t: BlockId) -> Option<usize> {
        let r = self.find(t);
        let only = !self.is_apart(r) && !self.others.contains_key(&r);
        only.then(|| self.gaps.get(&r).copied().unwrap_or(0))
    }

    /// Whether `name` was recorded as keeping its tree from shortest paths ([`Blocks::gap`]), in
    /// O(log n).
    pub fn is_gapped(&self, name: &str) -> bool {
        self.gapped.contains(name)
    }

    /// Records whether `name` keeps its tree from projection by shortest paths: in the scope,
    /// its integers lie in a class, or have holes wider than the gap its potential holds with
    /// at the name. [`Blocks::differences_only`] reads them, in O(log n).
    pub fn gap(&mut self, name: &Arc<str>, on: bool) {
        let changed = if on {
            self.gapped.insert(name.clone()).is_none()
        } else {
            self.gapped.remove(name).is_some()
        };
        if changed && let Some(&id) = self.name.get(name) {
            let r = self.find(id);
            tally(&mut self.gaps, r, if on { 1 } else { -1 });
        }
    }

    /// A new block of the conjuncts `gs`, none in a block, apart from the forest: no name or
    /// tree links it, so it is its own tree. In O(log n) per conjunct.
    pub fn detach(&mut self, gs: impl IntoIterator<Item = Arc<Formula>>) -> BlockId {
        let b = self.fresh();
        self.apart.insert(b);
        let mut ms = OrdSet::new();
        for g in gs {
            let was = self.put(&g, &g.atoms(), Some(b));
            debug_assert!(was.is_none(), "a conjunct detached is in no block");
            ms.insert(g);
        }
        self.members.insert(b, ms);
        b
    }

    /// Removes the block `b` made by [`Blocks::detach`].
    pub fn undetach(&mut self, b: BlockId) {
        debug_assert!(self.apart.contains(&b), "a block apart from the forest");
        for g in self.members.remove(&b).into_iter().flatten() {
            self.put(&g, &g.atoms(), None);
        }
        self.apart.remove(&b);
    }

    /// Decrements `names_in[b][n]` by 1, dropping empty inner maps, and returns its `moving_at`
    /// tag.
    fn dec_name_in(&mut self, b: BlockId, n: &Arc<str>) -> Option<BlockId> {
        let inner = self.names_in.get_mut(&b)?;
        let tag = match inner.get_mut(n) {
            Some((c, tag)) => {
                let tag = *tag;
                debug_assert!(*c > 0, "a count below zero");
                *c = c.saturating_sub(1);
                if *c == 0 {
                    inner.remove(n);
                }
                tag
            }
            None => {
                debug_assert!(false, "removing absent name from names_in");
                return None;
            }
        };
        if inner.is_empty() {
            self.names_in.remove(&b);
        }
        Some(tag)
    }

    /// Increments `names_in[b][n]` by 1 (initializing its `moving_at` tag to `b` when new)
    /// and returns its `moving_at` tag.
    fn inc_name_in(&mut self, b: BlockId, n: Arc<str>) -> BlockId {
        match self.names_in.get_mut(&b) {
            Some(inner) => match inner.get_mut(&n) {
                Some((c, tag)) => {
                    *c += 1;
                    *tag
                }
                None => {
                    inner.insert(n, (1, b));
                    b
                }
            },
            None => {
                self.names_in.insert(b, OrdMap::unit(n, (1, b)));
                b
            }
        }
    }

    /// Puts `g`, of the atoms `atoms`, in block `to`, or in none, and gives the block it was
    /// in; `of`, `at` and `forest` change together, a block apart from the forest being so
    /// already when a conjunct is put in it and still when one is taken out. In O(log n) per
    /// name of `g`.
    fn put(
        &mut self,
        g: &Arc<Formula>,
        atoms: &BTreeSet<Atom>,
        to: Option<BlockId>,
    ) -> Option<BlockId> {
        let raw_was = match to {
            Some(b) => self.of.insert(g.clone(), b),
            None => self.of.remove(g),
        };
        let was = raw_was.map(|w| self.resolve_mut(w));
        if was == to {
            return was;
        }
        // `atoms` are `g`'s atoms (each caller passes `g.atoms()`, or for `replace` those of a
        // conjunct of the same atoms), so its names are read from them, not collected again.
        for n in names_of_atoms(atoms) {
            let was_tag = was.and_then(|w| self.dec_name_in(w, &n));
            let to_tag = to.map(|t| self.inc_name_in(t, n.clone()));
            if self.hung.has(&n, g) {
                continue;
            }
            if let Some(tag) = was_tag {
                self.count_moving(&n, tag, -1);
            }
            if let Some(tag) = to_tag {
                self.count_moving(&n, tag, 1);
            }
        }
        let mut two = atoms.iter();
        if let (Some(Atom::Sym(u)), Some(Atom::Sym(v)), None) = (two.next(), two.next(), two.next())
        {
            if let Some(w) = was
                && let Some(inner) = self.pairs.get_mut(&w)
            {
                tally(inner, (u.clone(), v.clone()), -1);
                if inner.is_empty() {
                    self.pairs.remove(&w);
                }
            }
            if let Some(t) = to {
                match self.pairs.get_mut(&t) {
                    Some(inner) => tally(inner, (u.clone(), v.clone()), 1),
                    None => {
                        self.pairs
                            .insert(t, OrdMap::unit((u.clone(), v.clone()), 1));
                    }
                }
            }
        }
        let in_forest = |b: Option<BlockId>| b.is_some_and(|b| !self.apart.contains(&b));
        let (was_in, to_in) = (in_forest(was), in_forest(to));
        for a in atoms {
            let Atom::Sym(x) = a else {
                continue;
            };
            if was_in && !to_in {
                self.forest.remove_with(x, g, &mut self.last);
            } else if to_in && !was_in {
                self.forest.add_with(x, g, &mut self.last);
            }
            if let Some(w) = was
                && let Some(by_name) = self.at.get_mut(&w)
            {
                if let Some(set) = by_name.get_mut(x) {
                    set.remove(g);
                    if set.is_empty() {
                        by_name.remove(x);
                    }
                }
                if by_name.is_empty() {
                    self.at.remove(&w);
                }
            }
            if let Some(t) = to {
                match self.at.get_mut(&t) {
                    Some(by_name) => match by_name.get_mut(x) {
                        Some(set) => {
                            set.insert(g.clone());
                        }
                        None => {
                            by_name.insert(x.clone(), OrdSet::unit(g.clone()));
                        }
                    },
                    None => {
                        self.at
                            .insert(t, OrdMap::unit(x.clone(), OrdSet::unit(g.clone())));
                    }
                }
            }
        }
        was
    }

    // Complexity tradeoff: naive version, the name's counts taken out and put back, two
    // descents of O(log n) name comparisons. Used: one descent that changes them in place, a
    // second only for a name new to the map or one whose counts run out. COMPLEXITY.md row
    // ST-chain-raise-reverse-log.
    fn count_moving(&mut self, n: &Arc<str>, b: BlockId, by: isize) {
        match self.moving_at.get_mut(n) {
            Some(counts) => {
                tally(counts, b, by);
                if counts.is_empty() {
                    self.moving_at.remove(n);
                }
            }
            None => {
                let mut counts = OrdMap::new();
                tally(&mut counts, b, by);
                if !counts.is_empty() {
                    self.moving_at.insert(n.clone(), counts);
                }
            }
        }
    }

    /// Records that `g`, which mentions `n`, hangs at `n` as the hub of a star (`on`), or no
    /// longer does.
    pub fn hang(&mut self, n: &Arc<str>, g: &Arc<Formula>, on: bool) {
        let changed = self.hung.has(n, g) != on;
        if on {
            self.hung.add(n, g);
        } else {
            self.hung.remove(n, g);
        }
        if changed && let Some(b) = self.of_mut(g) {
            let tag = self
                .names_in
                .get(&b)
                .and_then(|m| m.get(n))
                .map_or(b, |&(_, tag)| tag);
            self.count_moving(n, tag, if on { -1 } else { 1 });
        }
    }

    /// The blocks that hold a moving conjunct of `n` ([`Conjuncts::moving`]), each once, in
    /// ascending order.
    pub fn moving_blocks(&self, n: &str) -> impl Iterator<Item = BlockId> + '_ {
        let Some(m) = self.moving_at.get(n) else {
            return MovingBlocks::Empty;
        };
        match m.len() {
            0 => MovingBlocks::Empty,
            1 => {
                let tag = *m.keys().next().expect("non-empty moving_at map");
                MovingBlocks::One(Some(self.resolve(tag)))
            }
            _ => {
                let mut ids: Vec<BlockId> = m.keys().map(|&tag| self.resolve(tag)).collect();
                ids.sort_unstable();
                MovingBlocks::Many(ids.into_iter())
            }
        }
    }

    fn fresh(&mut self) -> BlockId {
        self.next += 1;
        self.next
    }

    /// Checks the forest, for tests: each conjunct of the forest is in the block that holds
    /// it and each conjunct held is in a block, conjuncts that share an atom other than a name are
    /// in one block, each name is mentioned, and each name's conjuncts by block, and its moving
    /// conjuncts' counts by block ([`Blocks::moving_blocks`]), are those of the blocks; the parent
    /// links are exactly the pairs of a block and a name it mentions, each tree has one root
    /// that every node's links lead to, and the labels of the trees are those links'
    /// components; each tree's counts are those of its conjuncts and names.
    /// In time near the forest's size times its depth.
    pub fn well_formed(&self) -> Result<(), String> {
        // Check `uf` is acyclic and bounded in depth (union-by-rank guarantees <= 64).
        for (&id, _) in &self.uf {
            let mut cur = id;
            let mut steps = 0usize;
            while let Some(&node) = self.uf.get(&cur) {
                match node {
                    UfNode::Root { .. } => break,
                    UfNode::Parent(p) => {
                        steps += 1;
                        if steps > 64 {
                            return Err(format!("uf chain from {id} exceeds rank bound or cycles"));
                        }
                        cur = p;
                    }
                }
            }
        }
        let mut nodes: BTreeSet<BlockId> = BTreeSet::new();
        let mut names_of: BTreeMap<BlockId, BTreeSet<BlockId>> = BTreeMap::new();
        let mut others: BTreeMap<BlockId, usize> = BTreeMap::new();
        let mut gaps: BTreeMap<BlockId, usize> = BTreeMap::new();
        let mut at: BTreeMap<BlockId, BTreeMap<Arc<str>, BTreeSet<Arc<Formula>>>> = BTreeMap::new();
        let mut forest: BTreeMap<Arc<str>, BTreeSet<Arc<Formula>>> = BTreeMap::new();
        let mut total_members = 0usize;
        for (&b, ms) in &self.members {
            if ms.is_empty() {
                return Err(format!("block {b} has no conjuncts"));
            }
            if self.resolve(b) != b {
                return Err(format!("live block {b} resolves to {}", self.resolve(b)));
            }
            total_members += ms.len();
            for h in ms {
                if self.of(h) != Some(b) {
                    return Err(format!("{h} is in block {b} but not held there"));
                }
                for a in h.atoms() {
                    if let Atom::Sym(x) = a {
                        at.entry(b)
                            .or_default()
                            .entry(x)
                            .or_default()
                            .insert(h.clone());
                    }
                }
            }
            if self.apart.contains(&b) {
                if self.tree_of.contains_key(&b) || self.up.contains_key(&b) {
                    return Err(format!("block {b} apart from the forest is in a tree"));
                }
                continue;
            }
            for h in ms {
                for a in h.atoms() {
                    if let Atom::Sym(x) = a {
                        forest.entry(x).or_default().insert(h.clone());
                    }
                }
            }
            nodes.insert(b);
            let t = self.find(b);
            let mut ns = BTreeSet::new();
            for h in ms {
                if edges(h).is_none() {
                    *others.entry(t).or_default() += 1;
                }
                for a in h.atoms() {
                    match a {
                        Atom::Sym(n) => match self.name.get(&n) {
                            Some(&id) => {
                                ns.insert(id);
                            }
                            None => return Err(format!("{n} of {h} has no number")),
                        },
                        a => {
                            let gs = self.shared.get(&a).into_iter().flatten();
                            if let Some(o) = gs.map(|o| self.of(o)).find(|o| *o != Some(b)) {
                                return Err(format!("{h} of block {b} shares {a:?}, in {o:?}"));
                            }
                        }
                    }
                }
            }
            names_of.insert(b, ns);
        }
        // Each member is held in its own block, so no conjunct is in two; with as many
        // conjuncts held as there are members, no conjunct is held that is in no block.
        if self.of.len() != total_members {
            return Err("the conjuncts with a block are not those of the blocks".into());
        }
        let mut held_at: BTreeMap<BlockId, BTreeMap<Arc<str>, BTreeSet<Arc<Formula>>>> =
            BTreeMap::new();
        for (&b, by_name) in &self.at {
            if by_name.is_empty() {
                return Err(format!("empty `at` entry for block {b}"));
            }
            let mut inner = BTreeMap::new();
            for (n, s) in by_name {
                if s.is_empty() {
                    return Err(format!("empty `at` set for ({b}, {n})"));
                }
                inner.insert(n.clone(), s.iter().cloned().collect());
            }
            held_at.insert(b, inner);
        }
        if held_at != at {
            return Err("the conjuncts of the names by block are not those of the blocks".into());
        }
        let mut names_in: BTreeMap<BlockId, BTreeMap<Arc<str>, usize>> = BTreeMap::new();
        let mut pairs: BTreeMap<BlockId, BTreeMap<NamePair, usize>> = BTreeMap::new();
        let mut moving: BTreeMap<Arc<str>, BTreeMap<BlockId, usize>> = BTreeMap::new();
        for (&b, ms) in &self.members {
            for h in ms {
                for n in names(h) {
                    if !self.hung.has(&n, h) {
                        *moving.entry(n.clone()).or_default().entry(b).or_default() += 1;
                    }
                    *names_in.entry(b).or_default().entry(n).or_default() += 1;
                }
                if let Some([u, v]) = pair(h) {
                    *pairs.entry(b).or_default().entry((u, v)).or_default() += 1;
                }
            }
        }
        let mut held_names: BTreeMap<BlockId, BTreeMap<Arc<str>, usize>> = BTreeMap::new();
        for (&b, inner) in &self.names_in {
            if inner.is_empty() {
                return Err(format!("empty `names_in` entry for block {b}"));
            }
            let mut counts = BTreeMap::new();
            for (n, &(c, tag)) in inner {
                if c == 0 {
                    return Err(format!("zero `names_in` count for ({b}, {n})"));
                }
                if self.resolve(tag) != b {
                    return Err(format!(
                        "`names_in` tag {tag} for ({b}, {n}) resolves to {}",
                        self.resolve(tag)
                    ));
                }
                counts.insert(n.clone(), c);
            }
            held_names.insert(b, counts);
        }
        if held_names != names_in {
            return Err("the counts of the names of the blocks are not those of the blocks".into());
        }
        let mut held_pairs: BTreeMap<BlockId, BTreeMap<NamePair, usize>> = BTreeMap::new();
        for (&b, inner) in &self.pairs {
            if inner.is_empty() {
                return Err(format!("empty `pairs` entry for block {b}"));
            }
            let mut counts = BTreeMap::new();
            for (k, &c) in inner {
                if c == 0 {
                    return Err(format!("zero `pairs` count for ({b}, {k:?})"));
                }
                counts.insert(k.clone(), c);
            }
            held_pairs.insert(b, counts);
        }
        if held_pairs != pairs {
            return Err("the counts of the pairs of the blocks are not those of the blocks".into());
        }
        let mut kept_moving: BTreeMap<Arc<str>, BTreeMap<BlockId, usize>> = BTreeMap::new();
        for (n, m) in &self.moving_at {
            if m.is_empty() {
                return Err(format!("empty `moving_at` entry for {n}"));
            }
            let mut resolved = BTreeMap::new();
            for (&tag, &c) in m {
                if c == 0 {
                    return Err(format!("zero `moving_at` count for ({n}, {tag})"));
                }
                let b = self.resolve(tag);
                let expected_tag = self
                    .names_in
                    .get(&b)
                    .and_then(|im| im.get(n))
                    .map(|&(_, t)| t);
                if expected_tag != Some(tag) {
                    return Err(format!(
                        "`moving_at` tag {tag} for ({n}, {b}) mismatches `names_in` tag \
                         {expected_tag:?}"
                    ));
                }
                if resolved.insert(b, c).is_some() {
                    return Err(format!("duplicate resolved block {b} in `moving_at[{n}]`"));
                }
            }
            kept_moving.insert(n.clone(), resolved);
        }
        if kept_moving != moving {
            return Err(
                "the counts of the moving conjuncts of the names by block are not those of the \
                 blocks"
                    .into(),
            );
        }
        let held = (self.forest.0.iter()).map(|(k, s)| (k.clone(), s.iter().cloned().collect()));
        if !held.eq(forest) {
            return Err(
                "the conjuncts of the names in the forest are not those of its blocks".into(),
            );
        }
        for (n, &id) in &self.name {
            if self.syms.count(n) == 0 {
                return Err(format!("{n} is mentioned by no conjunct"));
            }
            nodes.insert(id);
            if self.gapped.contains(n) {
                *gaps.entry(self.find(id)).or_default() += 1;
            }
        }
        for &x in &nodes {
            let Some(t) = self.tree_of.get(&x) else {
                return Err(format!("node {x} has no tree"));
            };
            if !self.trees.get(t).is_some_and(|s| s.contains(&x)) {
                return Err(format!("node {x} is not among the nodes of its tree {t}"));
            }
        }
        let labeled: usize = self.trees.values().map(OrdSet::len).sum();
        if self.tree_of.len() != nodes.len() || labeled != nodes.len() {
            return Err(format!(
                "{} nodes, {} labels, {labeled} nodes of trees",
                nodes.len(),
                self.tree_of.len()
            ));
        }
        let mut links = 0;
        for (&b, ns) in &names_of {
            for &n in ns {
                if (self.parent(b) == Some(n)) == (self.parent(n) == Some(b)) {
                    return Err(format!("block {b} and its name {n} are not linked once"));
                }
                links += 1;
            }
        }
        if self.up.len() != links || self.up.keys().any(|k| !nodes.contains(k)) {
            return Err(format!(
                "parent links {:?}, names of the blocks {names_of:?}, names {:?}",
                self.up, self.name
            ));
        }
        let mut roots: BTreeMap<BlockId, BlockId> = BTreeMap::new();
        for &x in &nodes {
            let mut at = x;
            for _ in 0..=nodes.len() {
                match self.parent(at) {
                    Some(p) => at = p,
                    None => break,
                }
            }
            if self.parent(at).is_some() {
                return Err(format!("the links from {x} make a cycle"));
            }
            let t = self.find(x);
            if self.find(at) != t || *roots.entry(t).or_insert(at) != at {
                return Err(format!("node {x} of tree {t} leads to root {at}"));
            }
        }
        let counts = |kept: &OrdMap<BlockId, usize>| -> BTreeMap<BlockId, usize> {
            kept.iter().map(|(&t, &n)| (t, n)).collect()
        };
        if counts(&self.others) != others || counts(&self.gaps) != gaps {
            return Err(format!(
                "counts {:?} and {:?}, by the trees {others:?} and {gaps:?}",
                self.others, self.gaps
            ));
        }
        Ok(())
    }

    /// The tree of `x`, in O(log n): its label, or `x` itself for a block apart from the
    /// forest or a tree's own number.
    fn find(&self, x: BlockId) -> BlockId {
        self.tree_of.get(&x).copied().unwrap_or(x)
    }

    fn tree_size(&self, r: BlockId) -> usize {
        self.trees.get(&r).map_or(1, OrdSet::len)
    }

    /// Puts the new node `x` in tree `t`, or in a new tree of its own when `t` is `None`.
    fn new_node(&mut self, x: BlockId, t: Option<BlockId>) {
        let t = t.unwrap_or_else(|| self.fresh());
        self.tree_of.insert(x, t);
        self.trees.entry(t).or_default().insert(x);
    }

    /// Takes the node `x` out of its tree; a tree left with no node goes.
    fn drop_node(&mut self, x: BlockId) {
        let Some(t) = self.tree_of.remove(&x) else {
            return;
        };
        if let Some(s) = self.trees.get_mut(&t) {
            s.remove(&x);
            if s.is_empty() {
                self.trees.remove(&t);
                debug_assert!(
                    !self.others.contains_key(&t) && !self.gaps.contains_key(&t),
                    "a tree with no node has no count"
                );
            }
        }
    }

    /// Joins the trees of `a` and `b` by labeling the nodes of the smaller with the larger's
    /// number.
    // Complexity tradeoff: a union-find with parent links joins two trees in O(log n) but can
    // never split one, so a removal that splits a tree had to build its blocks again, in time
    // near the whole tree. Labels joined by relabeling the smaller tree cost O(s log n) for a
    // smaller tree of s nodes (O(log² n) amortized per node while trees only grow) and let a
    // split relabel the side it finds first ([`Blocks::bridge`]); a sequence that splits and
    // joins one large tree again and again pays near its smaller side each time.
    fn union(&mut self, a: BlockId, b: BlockId) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return;
        }
        let (small, big) = if self.tree_size(ra) < self.tree_size(rb) {
            (ra, rb)
        } else {
            (rb, ra)
        };
        let moved = self.trees.remove(&small).unwrap_or_default();
        for &x in &moved {
            self.tree_of.insert(x, big);
        }
        let into = self.trees.entry(big).or_default();
        *into = std::mem::take(into).union(moved);
        for counts in [&mut self.others, &mut self.gaps] {
            if let Some(n) = counts.remove(&small) {
                tally(counts, big, n as isize);
            }
        }
    }

    /// Makes `x` the root of its tree, reversing the parent links on its path to the root.
    fn reroot(&mut self, x: BlockId) {
        let mut prev: Option<BlockId> = None;
        let mut cur = x;
        loop {
            let next = self.parent_mut(cur);
            match prev {
                Some(p) => self.up.insert(cur, p),
                None => self.up.remove(&cur),
            };
            match next {
                Some(n) => {
                    prev = Some(cur);
                    cur = n;
                }
                None => break,
            }
        }
    }

    /// Joins the trees of `a` and `b`, two adjacent nodes of different trees, by rerooting the
    /// smaller at its node and hanging it from the other.
    fn join_trees(&mut self, a: BlockId, b: BlockId) {
        let (ra, rb) = (self.find(a), self.find(b));
        if self.tree_size(ra) <= self.tree_size(rb) {
            self.reroot(a);
            self.up.insert(a, b);
        } else {
            self.reroot(b);
            self.up.insert(b, a);
        }
        self.union(a, b);
    }

    /// The nodes of the tree path from `a` to `b`, two nodes of one tree, and the nearest
    /// common ancestor: both sides are walked up in turn until one meets the other's walk, in
    /// time near the path.
    fn path(&mut self, a: BlockId, b: BlockId) -> (Vec<BlockId>, BlockId) {
        let mut walks = [vec![a], vec![b]];
        let mut seen: [BTreeSet<BlockId>; 2] = [BTreeSet::from([a]), BTreeSet::from([b])];
        let top = if a == b {
            a
        } else {
            'walk: loop {
                let mut stepped = false;
                for side in 0..2 {
                    let last = *walks[side].last().expect("a start");
                    if let Some(p) = self.parent_mut(last) {
                        stepped = true;
                        walks[side].push(p);
                        seen[side].insert(p);
                        if seen[1 - side].contains(&p) {
                            break 'walk p;
                        }
                    }
                }
                assert!(stepped, "two nodes of one tree have a common ancestor");
            }
        };
        let [mut x, y] = walks;
        let cut = |w: &mut Vec<BlockId>| {
            let i = w.iter().position(|&n| n == top).expect("the ancestor");
            w.truncate(i + 1);
        };
        cut(&mut x);
        let mut y = y;
        cut(&mut y);
        y.pop();
        x.extend(y.into_iter().rev());
        (x, top)
    }

    /// Merges `blocks` into the one of the most conjuncts and gives it: the others' conjuncts
    /// and block-local indexes are unioned into it and merged-away ids recorded in `uf`. The
    /// merged block's parent is `top`.
    fn merge(&mut self, blocks: &[BlockId], top: Option<BlockId>) -> BlockId {
        let keep = *blocks
            .iter()
            .max_by_key(|&&b| self.members.get(&b).map_or(0, OrdSet::len))
            .expect("a block");
        // Complexity tradeoff: naive version, each conjunct of a merged block moved alone
        // ([`Blocks::put`]): per name of each conjunct, descents of `names_in`, `moving_at`,
        // `at` and `pairs`, each O(log n); a conjunct moves O(log n) times (each merge keeps the
        // block of the most conjuncts), so O(n log² n) over n conjuncts, 34% of the satellite of
        // every hub built in a random order and growing 11.40 times at 8n (presperf1). Stage 1
        // (satred1, 920b207e4): each index moved by its keys, not by conjunct, still
        // O(n log² n), merge alone growing 11.8 times at 8n and the bench 9.72. A move by keys
        // cannot do better while the indexes are keyed by name first: each name of the smaller
        // block is relabeled at its own place in the order, at least log C(N, k) comparisons
        // for k names among N, Θ(n log² n) over merges of blocks of equal size (cross-review
        // round 1, Opus and Sol seats). Used (cross-review round 1, Gemini seat): (1) the
        // block-local indexes (`members`, `names_in`, `at`, `pairs`) are nested by `BlockId`
        // and merged with the join-based B+Tree `union`/`union_with_key` added to
        // `vendor/imbl` (Blelloch, Ferizovic and Sun, "Just Join for Parallel Ordered Sets",
        // SPAA 2016, doi:10.1145/2935764.2935768, arXiv:1602.02120), O(m log(n/m + 1)) for m
        // keys into n, which sums to O(n log n) over any merge tree (Brown and Tarjan, "A fast
        // merging algorithm", JACM 26(2), 1979, doi:10.1145/322123.322127, sec. 4, p. 225,
        // stated without proof; both papers read 2026-11-21, the proof by the product of
        // binomials is in the crate's `lib.rs`, "References"); (2) the indexes
        // keyed by conjunct or name (`of`, `up`, `moving_at`) are not rewritten:
        // `uf_merge(b, keep)` records `b -> keep` in the persistent union-find `uf` (union by
        // rank, path compression on `&mut self`; Tarjan, JACM 22(2), 1975,
        // doi:10.1145/321879.321884), O(log n) per merged-away block, and a read resolves its
        // block through `uf`; `moving_at` is keyed by stable tags (`names_in`'s second field)
        // and changed only for the names both blocks hold, which `names_in`'s
        // `union_with_key` finds, at most one per name per merge it survives. Cost: a read of
        // `of`, `up` or `moving_at` follows at most log₂ n `uf` links when not compressed;
        // `moving_blocks(n)` resolves tags and sorts when `n` is in two or more blocks; `uf`
        // is never compacted, so it keeps one entry per merged-away block; `Blocks::union`
        // still relabels the smaller tree of `tree_of` node by node, O(n log² n) over unions
        // (about 2% of the satellite bench's run, Opus seat). Merge alone now grows 9.06
        // times at 8n (callgrind, Gemini seat; 11.7 before), and
        // `stars_formed_in_the_block_of_a_satellite_take_time_near_the_block` 9.336 (9.763
        // before). COMPLEXITY.md row PERF-satellite-random-under9-redesign.
        let mut keep_members = self.members.remove(&keep).unwrap_or_default();
        let mut keep_names = self.names_in.remove(&keep).unwrap_or_default();
        let mut keep_at = self.at.remove(&keep).unwrap_or_default();
        let mut keep_pairs = self.pairs.remove(&keep).unwrap_or_default();
        for &b in blocks.iter().filter(|&&b| b != keep) {
            debug_assert!(
                !self.apart.contains(&b) && !self.apart.contains(&keep),
                "only blocks of the forest are merged, so `forest` keeps its entries"
            );
            self.uf_merge(b, keep);
            if let Some(moved) = self.members.remove(&b) {
                keep_members = keep_members.union(moved);
            }
            if let Some(b_names) = self.names_in.remove(&b) {
                let moving_at = &mut self.moving_at;
                keep_names = keep_names.union_with_key(b_names, |n, (ck, tag_k), (cb, tag_b)| {
                    if let Some(counts) = moving_at.get_mut(n)
                        && let Some(m) = counts.remove(&tag_b)
                    {
                        tally(counts, tag_k, m as isize);
                    }
                    (ck + cb, tag_k)
                });
            }
            if let Some(b_at) = self.at.remove(&b) {
                keep_at = keep_at.union_with(b_at, |a, b| a.union(b));
            }
            if let Some(b_pairs) = self.pairs.remove(&b) {
                keep_pairs = keep_pairs.union_with(b_pairs, |a, b| a + b);
            }
            self.up.remove(&b);
            self.drop_node(b);
        }
        if !keep_members.is_empty() {
            self.members.insert(keep, keep_members);
        }
        if !keep_names.is_empty() {
            self.names_in.insert(keep, keep_names);
        }
        if !keep_at.is_empty() {
            self.at.insert(keep, keep_at);
        }
        if !keep_pairs.is_empty() {
            self.pairs.insert(keep, keep_pairs);
        }
        match top {
            Some(t) => self.up.insert(keep, t),
            None => self.up.remove(&keep),
        };
        keep
    }

    /// Puts `a` and `b`, two blocks or names, in one block: the blocks on their tree path are
    /// merged, or, when they lie in different trees, the smaller tree is rerooted at its node
    /// and its block merged with the other's. `a` is a block; the block that holds its
    /// conjuncts afterward is returned.
    fn unite(&mut self, a: BlockId, b: BlockId) -> BlockId {
        if self.find(a) != self.find(b) {
            // Two blocks of different trees, which share an atom other than a name.
            let small_first = self.tree_size(self.find(a)) <= self.tree_size(self.find(b));
            let (x, y) = if small_first { (a, b) } else { (b, a) };
            self.reroot(x);
            let top = self.parent_mut(y);
            // Before the merge, which takes one of the two blocks out of its tree.
            self.union(a, b);
            return self.merge(&[x, y], top);
        }
        let (path, top) = self.path(a, b);
        let (blocks, names): (Vec<BlockId>, Vec<BlockId>) = path
            .iter()
            .copied()
            .partition(|n| self.members.contains_key(n));
        if blocks.len() < 2 {
            return a;
        }
        let parent = if self.members.contains_key(&top) {
            self.parent_mut(top)
        } else {
            Some(top)
        };
        let keep = self.merge(&blocks, parent);
        // The names of the path, told apart before the merge: the blocks it merges away are
        // no blocks after it, and linking them again left links of blocks gone in `up`.
        for n in names.into_iter().filter(|&n| n != top) {
            self.up.insert(n, keep);
        }
        keep
    }

    /// Places `g`, already indexed by its atoms, in the forest.
    fn place(&mut self, g: &Arc<Formula>) {
        let b = self.fresh();
        self.members.insert(b, OrdSet::unit(g.clone()));
        let atoms = g.atoms();
        self.put(g, &atoms, Some(b));
        self.new_node(b, None);
        if edges(g).is_none() {
            let r = self.find(b);
            tally(&mut self.others, r, 1);
        }
        let mut met: Vec<BlockId> = Vec::new();
        for a in &atoms {
            if let Atom::Sym(n) = a {
                match self.name.get(n) {
                    Some(&id) => met.push(id),
                    None => {
                        let id = self.fresh();
                        self.name.insert(n.clone(), id);
                        self.up.insert(id, b);
                        let r = self.find(b);
                        self.new_node(id, Some(r));
                        if self.gapped.contains(n) {
                            tally(&mut self.gaps, r, 1);
                        }
                    }
                }
            }
        }
        // The block that holds `g`, kept here: looking `g` up again would compare it whole.
        let mut cur = b;
        for id in met {
            if self.find(cur) == self.find(id) {
                cur = self.unite(cur, id);
            } else {
                self.join_trees(cur, id);
            }
        }
        for a in atoms.iter().filter(|a| !matches!(a, Atom::Sym(_))) {
            let other = self
                .shared
                .get(a)
                .and_then(|s| s.iter().find(|h| *h != g))
                .and_then(|h| self.of.get(h))
                .copied()
                .map(|raw| self.resolve_mut(raw));
            if let Some(o) = other
                && o != cur
            {
                cur = self.unite(cur, o);
            }
        }
    }

    /// Adds the conjunct `g`.
    pub fn add(&mut self, g: &Arc<Formula>) {
        for a in g.atoms() {
            match a {
                Atom::Sym(n) => self.syms.add_with(&n, g, &mut self.last),
                a => {
                    self.shared.entry(a).or_default().insert(g.clone());
                }
            }
        }
        self.place(g);
    }

    /// Puts `new` in the place of `old`, a conjunct of the same atoms.
    pub fn replace(&mut self, old: &Arc<Formula>, new: &Arc<Formula>) {
        let atoms = old.atoms();
        debug_assert_eq!(
            atoms,
            new.atoms(),
            "replace takes a conjunct of the same atoms"
        );
        let Some(b) = self.put(old, &atoms, None) else {
            return self.add(new);
        };
        self.put(new, &atoms, Some(b));
        if let Some(m) = self.members.get_mut(&b) {
            m.remove(old);
            m.insert(new.clone());
        }
        let by = isize::from(edges(new).is_none()) - isize::from(edges(old).is_none());
        if by != 0 && !self.is_apart(b) {
            let r = self.find(b);
            tally(&mut self.others, r, by);
        }
        for a in atoms {
            match a {
                Atom::Sym(n) => {
                    self.syms.remove(&n, old);
                    self.syms.add(&n, new);
                }
                a => {
                    if let Some(s) = self.shared.get_mut(&a) {
                        s.remove(old);
                        s.insert(new.clone());
                    }
                }
            }
        }
    }

    /// Removes the conjuncts `gs`, block by block. A conjunct of two names and no other atom is
    /// taken out alone (`Blocks::cut`), in time near the smaller side of each split it makes.
    /// Otherwise a block that loses its one conjunct, which shares at most one name and no
    /// other atom with the rest, is unlinked; a block that loses some of its conjuncts is split
    /// once by placing its other conjuncts again (`Blocks::split`); if that fails, the blocks of
    /// every conjunct linked to one of `gs` are built again. Each such block is split once for
    /// all the conjuncts it loses, so a removal costs near the blocks it touches, not their
    /// size times the conjuncts removed.
    // Complexity tradeoff: naive version, the block is split once per conjunct removed, each
    // split placing the block's other conjuncts again, and `place` and `split` look a placed
    // disjunction up in `of` once per name it mentions, each lookup comparing the whole
    // disjunction: O(k³) for a join of two arms on k disjoint groups (26 ms → 6.26 s at
    // k = 8 → 64). Used: the removed conjuncts are grouped by block and each block is split
    // once for all it loses; `unite` returns the block it places into, so no lookup repeats:
    // near linear (1.5 → 17.2 ms). Tradeoffs: one `BTreeMap` of the removed conjuncts per
    // call; a failed split rebuilds the blocks of every conjunct linked to `gs`. Results are
    // byte for byte those of the old code on 600 random joins. Tests:
    // `l01_39_scope_relations::disjoint::the_join_of_arms_on_many_disjoint_groups_scales` and
    // `disjoint::the_blocks_of_a_join_are_those_of_the_definition`; COMPLEXITY.md row S29.
    pub fn remove(&mut self, gs: &[Arc<Formula>]) {
        // The conjuncts removed from each block, the blocks in the order `gs` first meets them.
        let mut from: BTreeMap<BlockId, Vec<&Arc<Formula>>> = BTreeMap::new();
        let mut order: Vec<BlockId> = Vec::new();
        for g in gs {
            match self.of_mut(g) {
                Some(b) => {
                    let out = from.entry(b).or_default();
                    if out.is_empty() {
                        order.push(b);
                    }
                    out.push(g);
                }
                None => self.unuse(g),
            }
        }
        let mut rebuild = false;
        for b in order {
            let out = &from[&b];
            if !rebuild && !self.is_apart(b) {
                let pairs: Option<Vec<[Arc<str>; 2]>> = out.iter().map(|g| pair(g)).collect();
                if let Some(pairs) = pairs {
                    for (g, [u, v]) in out.iter().zip(pairs) {
                        self.unuse(g);
                        let b = self.of_mut(g).expect("the block of a conjunct");
                        self.cut(b, g, &u, &v);
                    }
                    continue;
                }
            }
            for g in out {
                self.unuse(g);
            }
            if rebuild {
                continue;
            }
            match out[..] {
                [g] if self.unlink(b, g) => {}
                _ if !self.is_apart(b) && self.remove_covered(b, out) => {}
                _ => rebuild = !self.split(b, out),
            }
        }
        if rebuild {
            self.rebuild(gs);
        }
    }

    /// Takes `g`, a conjunct of the two names `u` and `v` and no other atom, already out of
    /// `syms`, out of its block `b` of the forest. Alone in `b`, it is unlinked when one of its
    /// names is mentioned no more, and otherwise its tree splits in two ([`Blocks::bridge`]);
    /// with other conjuncts, `b` splits into a path of blocks ([`Blocks::peel`]).
    fn cut(&mut self, b: BlockId, g: &Arc<Formula>, u: &Arc<str>, v: &Arc<str>) {
        if self.unlink(b, g) {
            return;
        }
        let r = self.find(b);
        if edges(g).is_none() {
            tally(&mut self.others, r, -1);
        }
        self.put(g, &g.atoms(), None);
        let ms = self.members.get_mut(&b).expect("the block of a conjunct");
        ms.remove(g);
        let (iu, iv) = (self.name[u], self.name[v]);
        // Another conjunct of `u` and `v` alone in `b` takes `g`'s place on any cycle through `g`
        // but the one through both, whose edges meet at it: `b` stays one block (the count
        // `pairs`).
        if ms.is_empty() {
            self.bridge(b, r, (u, iu), (v, iv));
        } else if !self
            .pairs
            .get(&b)
            .is_some_and(|m| m.contains_key(&(u.clone(), v.clone())))
        {
            self.peel(b, r, (u, iu), (v, iv));
        }
    }

    /// Takes block `b` of tree `r`, emptied of its one conjunct, which linked the names `u` and
    /// `v` that other conjuncts still mention, out of the forest: the tree splits into the
    /// side of `u` and the side of `v`. Both sides are walked one entry at a time in turn, and
    /// the side found whole first takes a new tree number, with its counts.
    // Complexity tradeoff: building the blocks of the tree again, as a removal that split a
    // tree did before, costs near the whole tree, O(n log² n). Walking both sides in turn costs
    // O(s log n) for the smaller side of s entries (twice the smaller at most), and the labels
    // of [`Blocks::union`] let that side alone be relabeled; the larger side is not read.
    fn bridge(&mut self, b: BlockId, r: BlockId, u: (&Arc<str>, BlockId), v: (&Arc<str>, BlockId)) {
        self.members.remove(&b);
        self.up.remove(&b);
        for id in [u.1, v.1] {
            if self.parent_mut(id) == Some(b) {
                self.up.remove(&id);
            }
        }
        self.drop_node(b);
        let mut walks = [TreeWalk::new(u), TreeWalk::new(v)];
        let side = 'walk: loop {
            for (i, w) in walks.iter_mut().enumerate() {
                if !w.step(self) {
                    break 'walk i;
                }
            }
        };
        let [first, second] = walks;
        let TreeWalk { nodes, .. } = if side == 0 { first } else { second };
        let t = self.fresh();
        let (mut others, mut gaps) = (0isize, 0isize);
        for (x, name) in &nodes {
            match name {
                Some(n) => gaps += isize::from(self.gapped.contains(n)),
                None => {
                    others += self.members(*x).filter(|h| edges(h).is_none()).count() as isize;
                }
            }
            self.tree_of.insert(*x, t);
            if let Some(s) = self.trees.get_mut(&r) {
                s.remove(x);
            }
        }
        let nodes: OrdSet<BlockId> = nodes.iter().map(|(x, _)| *x).collect();
        self.trees.insert(t, nodes);
        for (counts, by) in [(&mut self.others, others), (&mut self.gaps, gaps)] {
            tally(counts, r, -by);
            tally(counts, t, by);
        }
    }

    /// Takes the conjunct of the names `u` and `v`, already out of the indexes, out of block
    /// `b` of tree `r`, which keeps other conjuncts. `b` was one block with it, so without it
    /// the blocks are a path from the block of `u` to the block of `v`, each two consecutive
    /// ones sharing a name that every path from `u` to `v` crosses. A first path `P` from `u`
    /// to `v` within `b` is found by a search from both ends that meets in the middle. The
    /// names on `P` that cut `u` from `v` are those a flow of two along paths from `u` to `v`
    /// that share no name cannot pass: a search for a second path in the residual graph of `P`
    /// from `u` and one from `v` toward `u`, run one entry at a time in turn, stop when either
    /// meets its end, which leaves one block, or runs out first; the conjuncts it reached are
    /// the end block, cut at the name of `P` it entered and could not leave, which is given a
    /// new number before the searches start again from that name. The block left last keeps
    /// `b`; then the parent links are set along the path, from `b`'s parent.
    ///
    /// Proof that the blocks left are such a path: `b` is biconnected and holds a conjunct
    /// besides `g`, the one taken out, so any two of its conjuncts lie on one cycle (Menger's
    /// theorem: two paths sharing no name join the ends of one to the ends of the other), and
    /// each conjunct `e` of `b` lies on a cycle through `g`, so on a path from `u` to `v` in `b`
    /// without `g`. A path from `u` to `v` passes, in the tree of blocks and cut names of `b`
    /// without `g`, through exactly the blocks on the tree path from a block of `u` to one of
    /// `v`, and through each name joining two consecutive ones. So every conjunct is in a block
    /// of that tree path, no block is off it, and each name joining two of them is on every path
    /// from `u` to `v`, which is the cut the flow of two finds.
    // Complexity tradeoff: placing the block's other conjuncts again (`Blocks::split`) costs
    // O(|b| log n) for each conjunct taken out, so O(d²) to take apart a block of d conjuncts
    // one at a time. The searches cost O((|P| + c + s) log n), where c is the size of the blocks
    // split off, each found by the search that ran out first, so at most twice the smaller side
    // at its cut, and s the cost of the last search, which met its end; a block only taken
    // apart then costs O(d log² n) in all, each conjunct moving to a new block on the smaller
    // side. Still near the block each time: taking a chord out of a long cycle, which leaves
    // one block, when `P` or the meeting search is long, and a name of many conjuncts in other
    // blocks, whose entries the searches pass over. Holm, de Lichtenberg and Thorup's dynamic
    // biconnectivity (J. ACM 48(4), 2001, doi:10.1145/502090.502095, read 2026-11-21;
    // Theorem 23, O(log⁵ n) amortized per insertion, deletion or query) bounds every case, at
    // the cost of a far larger structure: a spanning forest kept in levels with top trees, and
    // for each nontree edge the triples `xyz` of its cycle that it covers (sec. 7). It answers
    // whether two vertices are biconnected; it does not list a block's conjuncts, which `peel`
    // must produce, so taking it would need that listing added. See `lib.rs`, "References".
    fn peel(&mut self, b: BlockId, r: BlockId, u: (&Arc<str>, BlockId), v: (&Arc<str>, BlockId)) {
        let path = self.route(
            b,
            Node::Name(u.0.clone(), u.1),
            Node::Name(v.0.clone(), v.1),
        );
        let at: HashMap<Key, usize> = path.iter().enumerate().map(|(i, n)| (n.key(), i)).collect();
        // The blocks split off at either end, each with the position on `P` of its cut.
        let mut ends: [Vec<(BlockId, usize)>; 2] = [Vec::new(), Vec::new()];
        let (mut lo, mut hi) = (0, path.len() - 1);
        loop {
            let mut flows = [Flow::new(&path, lo, hi), Flow::new(&path, hi, lo)];
            let ran_out = 'search: loop {
                for (i, f) in flows.iter_mut().enumerate() {
                    match f.step(self, b, &path, &at) {
                        Step::On => {}
                        Step::Met => break 'search None,
                        Step::Out(cut) => break 'search Some((i, cut)),
                    }
                }
            };
            let Some((i, cut)) = ran_out else { break };
            let [first, second] = flows;
            let Flow { conjs, .. } = if i == 0 { first } else { second };
            let nb = self.fresh();
            let ms = self.members.get_mut(&b).expect("the block split");
            for h in &conjs {
                ms.remove(h);
            }
            for h in &conjs {
                self.put(h, &h.atoms(), Some(nb));
            }
            self.members.insert(nb, conjs.into_iter().collect());
            self.new_node(nb, Some(r));
            ends[i].push((nb, cut));
            if i == 0 {
                lo = cut;
            } else {
                hi = cut;
            }
        }
        // The blocks from `u`'s end to `v`'s, and the names between each two.
        let [left, right] = ends;
        let mut seq: Vec<BlockId> = left.iter().map(|&(nb, _)| nb).collect();
        seq.push(b);
        seq.extend(right.iter().rev().map(|&(nb, _)| nb));
        let cut_id = |i: usize| match &path[i] {
            Node::Name(_, id) => *id,
            _ => unreachable!("a cut is a name"),
        };
        let cuts: Vec<BlockId> = left
            .iter()
            .chain(right.iter().rev())
            .map(|&(_, c)| cut_id(c))
            .collect();
        let parent = self.parent_mut(b);
        // The block that hangs from `b`'s parent: the one after it when it is a cut, so that the
        // one before hangs from it too; else the one that mentions it, else `b`.
        let mut top = left.len();
        if let Some(p) = parent
            && let Some(i) = cuts.iter().position(|&c| c == p)
        {
            top = i + 1;
        }
        let is_cut: HashSet<BlockId> = cuts.iter().copied().collect();
        for (i, &nb) in seq.iter().enumerate() {
            if nb == b {
                continue;
            }
            let ms: Vec<Arc<Formula>> = self.members(nb).cloned().collect();
            for h in ms {
                for a in h.atoms() {
                    let Atom::Sym(n) = a else { continue };
                    let id = self.name[&n];
                    if Some(id) == parent {
                        if !is_cut.contains(&id) {
                            top = i;
                        }
                    } else if !is_cut.contains(&id) {
                        self.up.insert(id, nb);
                    }
                }
            }
        }
        for (i, &nb) in seq.iter().enumerate() {
            let (link, next) = match i.cmp(&top) {
                std::cmp::Ordering::Equal => {
                    match parent {
                        Some(p) => self.up.insert(nb, p),
                        None => self.up.remove(&nb),
                    };
                    continue;
                }
                std::cmp::Ordering::Less => (cuts[i], seq[i + 1]),
                std::cmp::Ordering::Greater => (cuts[i - 1], seq[i - 1]),
            };
            self.up.insert(nb, link);
            if Some(link) != parent {
                self.up.insert(link, next);
            }
        }
    }

    /// A path from `u` to `v`, two nodes of block `b`, within `b`: a breadth-first search from
    /// each end, one entry at a time in turn, until one reaches a node the other has.
    fn route(&self, b: BlockId, u: Node, v: Node) -> Vec<Node> {
        let mut sides = [Search::new(u), Search::new(v)];
        let (k0, k1) = 'search: loop {
            for i in 0..2 {
                let [s0, s1] = &mut sides;
                let (me, other) = if i == 0 { (s0, s1) } else { (s1, s0) };
                match me.step(self, b) {
                    None => {}
                    Some((from, k, n)) => {
                        if other.seen.contains_key(&k) {
                            break 'search if i == 0 { (from, k) } else { (k, from) };
                        }
                        if !me.seen.contains_key(&k) {
                            me.seen.insert(k.clone(), (n, Some(from)));
                            me.queue.push_back(k);
                        }
                    }
                }
                assert!(
                    me.cur.is_some() || !me.queue.is_empty(),
                    "two names of a block of two conjuncts or more are linked within it"
                );
            }
        };
        let [s0, s1] = sides;
        let mut path = s0.chain(k0);
        path.reverse();
        path.extend(s1.chain(k1));
        path
    }

    /// Takes `g` out of the index of the atoms it mentions.
    fn unuse(&mut self, g: &Arc<Formula>) {
        for a in g.atoms() {
            match a {
                Atom::Sym(n) => self.syms.remove_with(&n, g, &mut self.last),
                a => {
                    if let Some(s) = self.shared.get_mut(&a) {
                        s.remove(g);
                        if s.is_empty() {
                            self.shared.remove(&a);
                        }
                    }
                }
            }
        }
    }

    /// Unlinks `g`, already out of `syms` and `shared`, from the forest when it is its block
    /// `b` alone and shares at most one name and no other atom with the rest; whether it was.
    fn unlink(&mut self, b: BlockId, g: &Arc<Formula>) -> bool {
        let atoms = g.atoms();
        let alone = self.members.get(&b).is_some_and(|m| m.len() == 1);
        let apart = atoms
            .iter()
            .all(|a| matches!(a, Atom::Sym(_)) || !self.shared.contains_key(a));
        let kept: Vec<&Arc<str>> = atoms
            .iter()
            .filter_map(|a| match a {
                Atom::Sym(n) => Some(n),
                _ => None,
            })
            .filter(|n| self.syms.of(n).next().is_some())
            .collect();
        if !(alone && apart && kept.len() <= 1) {
            return false;
        }
        let r = self.find(b);
        let counted = !self.is_apart(r);
        if counted && edges(g).is_none() {
            tally(&mut self.others, r, -1);
        }
        for a in &atoms {
            if let Atom::Sym(n) = a
                && kept.first() != Some(&n)
                && let Some(id) = self.name.remove(n)
            {
                self.up.remove(&id);
                if counted && self.gapped.contains(n) {
                    tally(&mut self.gaps, r, -1);
                }
                self.drop_node(id);
            }
        }
        if let Some(s) = kept.first()
            && let Some(&id) = self.name.get(*s)
            && self.parent_mut(id) == Some(b)
        {
            self.up.remove(&id);
        }
        self.up.remove(&b);
        self.members.remove(&b);
        self.drop_node(b);
        self.put(g, &g.atoms(), None);
        true
    }

    /// Removes `out` (already taken out of `syms`) from non-apart block `b` in O(|out| s log k)
    /// when every `g` in `out` mentions plain names only and another remaining conjunct `h` in
    /// `b` covers all of `g`'s atoms (`atoms(g) ⊆ atoms(h)`).
    ///
    /// Proof: in [`Blocks`], two conjuncts are in the same block iff no name vertex separates
    /// them in the bipartite graph of conjuncts and names (components sharing a conjunct vertex
    /// merge into one block). For any name vertex `u`, any path in `G \ {u}` passing through
    /// `n1 - g - n2` has `n1, n2 ∈ atoms(g) \ {u} ⊆ atoms(h) \ {u}`, so `n1 - h - n2` is a walk
    /// in `(G \ out) \ {u}`. By induction over `g ∈ out` (each witness `h` is in `b \ out`, as
    /// `syms` no longer holds `out`), neither connectivity modulo any name nor the set of names
    /// of `b` changes, so `b` stays one block with the same tree links.
    // Complexity tradeoff: naive version, `Blocks::split` rebuilds all `m` members of `b`
    // whenever a removed conjunct has 3+ names (`pair(g)` is `None`), O(m log^2 m) per join and
    // O(k^2 log^2 k) on `split4` (2,142 member re-insertions at k = 64 vs 42 at k = 8). Used:
    // probe the first and last remaining conjunct of `syms` for each name of `g`, O(s log k)
    // per removed conjunct; falls back to `split` when no single witness covers `g`.
    // COMPLEXITY.md PERF-refused-shape-disjunctions-quadratic.
    fn remove_covered(&mut self, b: BlockId, out: &[&Arc<Formula>]) -> bool {
        let mut atom_sets: Vec<BTreeSet<Atom>> = Vec::with_capacity(out.len());
        for g in out {
            let atoms = g.atoms();
            if atoms.is_empty() || !atoms.iter().all(|a| matches!(a, Atom::Sym(_))) {
                return false;
            }
            let covered = atoms.iter().any(|a| {
                let Atom::Sym(n) = a else { return false };
                let Some(s) = self.syms.0.get(n) else {
                    return false;
                };
                [s.get_min(), s.get_max()]
                    .into_iter()
                    .flatten()
                    .any(|h| self.of(h) == Some(b) && atoms.is_subset(&h.atoms()))
            });
            if !covered {
                return false;
            }
            atom_sets.push(atoms);
        }
        let r = self.find(b);
        for (g, atoms) in out.iter().zip(atom_sets) {
            if edges(g).is_none() {
                tally(&mut self.others, r, -1);
            }
            self.put(g, &atoms, None);
            let ms = self.members.get_mut(&b).expect("the block of a conjunct");
            ms.remove(*g);
        }
        true
    }

    /// Removes `out`, conjuncts of block `b` already out of `syms`, from it by placing the
    /// block's other conjuncts again, in time near the block's size, when that keeps the tree
    /// whole: every atom of the block is a name, and the other conjuncts link every name of
    /// the block that some conjunct still mentions. Removing `b` from the tree leaves one piece
    /// per name of it, all under one tree label, which cannot split; the pieces of
    /// the names `b` is the parent of are rooted at those names, so linking a piece to the rest
    /// reroots it within the block's nodes only. Whether it did; if not, nothing is changed.
    fn split(&mut self, b: BlockId, out: &[&Arc<Formula>]) -> bool {
        let Some(ms) = self.members.get(&b) else {
            return false;
        };
        let gone: BTreeSet<&Arc<Formula>> = out.iter().copied().collect();
        let rest: Vec<(Arc<Formula>, Vec<Arc<str>>)> = ms
            .iter()
            .filter(|h| !gone.contains(h))
            .map(|h| {
                let names = h.atoms().into_iter().filter_map(|a| match a {
                    Atom::Sym(n) => Some(n),
                    _ => None,
                });
                (h.clone(), names.collect())
            })
            .collect();
        if rest.is_empty() {
            return false;
        }
        if ms
            .iter()
            .any(|h| h.atoms().iter().any(|a| !matches!(a, Atom::Sym(_))))
        {
            return false;
        }
        // The names of the block, each with its place in a union-find over them.
        let mut index: BTreeMap<Arc<str>, usize> = BTreeMap::new();
        for h in ms.iter() {
            for n in names(h) {
                let i = index.len();
                index.entry(n).or_insert(i);
            }
        }
        // Halving with rank (the root that stays is rank's): O(α(n)) amortized a step, Tarjan and
        // van Leeuwen 1984 (doi:10.1145/62.2160), Theorem 3; halving walks the path once.
        let mut parent = zed_graph::UnionFind::new(
            index.len(),
            zed_graph::Compression::Halving,
            zed_graph::Linking::Rank,
        );
        let mut used = vec![false; index.len()];
        for (_, ns) in &rest {
            let first = index[&ns[0]];
            for n in ns {
                let i = index[n];
                used[i] = true;
                parent.union(first, i);
            }
        }
        let mut whole = None;
        for (n, &i) in &index {
            let still = self.syms.of(n).next().is_some();
            if !still {
                continue;
            }
            let r = parent.find(i);
            if !used[i] || whole.is_some_and(|w| w != r) {
                return false;
            }
            whole = Some(r);
        }
        // The tree stays whole: take `b` out and place its other conjuncts again.
        let top = self.up.remove(&b);
        self.members.remove(&b);
        let r = self.find(b);
        self.drop_node(b);
        for (h, _) in &rest {
            self.put(h, &h.atoms(), None);
        }
        for g in out {
            self.put(g, &g.atoms(), None);
        }
        // The local pieces: each kept name of the block and each new block, with the piece
        // that holds `top`, which hangs from the rest of the tree, never rerooted.
        let mut piece: BTreeMap<BlockId, BlockId> = BTreeMap::new();
        let mut count: BTreeMap<BlockId, usize> = BTreeMap::new();
        // The conjuncts and names the tree loses that its counts hold.
        let others = out.iter().filter(|g| edges(g).is_none()).count();
        let mut gaps = 0usize;
        for n in index.keys() {
            let Some(&id) = self.name.get(n) else {
                continue;
            };
            if self.syms.of(n).next().is_none() {
                self.name.remove(n);
                self.up.remove(&id);
                self.drop_node(id);
                gaps += usize::from(self.gapped.contains(n));
                continue;
            }
            if self.parent_mut(id) == Some(b) {
                self.up.remove(&id);
            }
            count.insert(id, if Some(id) == top { usize::MAX } else { 1 });
        }
        fn find(piece: &BTreeMap<BlockId, BlockId>, mut x: BlockId) -> BlockId {
            while let Some(&p) = piece.get(&x) {
                x = p;
            }
            x
        }
        for (h, ns) in &rest {
            let nb = self.fresh();
            self.members.insert(nb, OrdSet::unit(h.clone()));
            self.put(h, &h.atoms(), Some(nb));
            self.new_node(nb, Some(r));
            count.insert(nb, 1);
            // The block that holds `h`.
            let mut cur = nb;
            for n in ns {
                let id = self.name[n];
                let (pc, pi) = (find(&piece, cur), find(&piece, id));
                if pc == pi {
                    cur = self.unite(cur, id);
                    continue;
                }
                // Reroot the smaller piece at its node and hang it from the other's.
                let (sc, si) = (count[&pc], count[&pi]);
                let ((x, px), (y, py)) = if sc <= si {
                    ((cur, pc), (id, pi))
                } else {
                    ((id, pi), (cur, pc))
                };
                self.reroot(x);
                self.up.insert(x, y);
                piece.insert(px, py);
                let s = count[&px].saturating_add(count[&py]);
                count.insert(py, s);
            }
        }
        // The tree lost `b` and the names no conjunct mentions, and gained the new blocks.
        tally(&mut self.others, r, -(others as isize));
        tally(&mut self.gaps, r, -(gaps as isize));
        true
    }

    /// Builds again the blocks of the conjuncts linked to one of `gs`, which are removed.
    fn rebuild(&mut self, gs: &[Arc<Formula>]) {
        let mut names: Vec<Arc<str>> = Vec::new();
        let mut atoms: Vec<Atom> = Vec::new();
        let mut seen_names: BTreeSet<Arc<str>> = BTreeSet::new();
        let mut seen_atoms: BTreeSet<Atom> = BTreeSet::new();
        let mut found: BTreeSet<Arc<Formula>> = BTreeSet::new();
        let mut visit = |a: Atom, names: &mut Vec<_>, atoms: &mut Vec<_>| match a {
            Atom::Sym(n) => {
                if seen_names.insert(n.clone()) {
                    names.push(n);
                }
            }
            a => {
                if seen_atoms.insert(a.clone()) {
                    atoms.push(a);
                }
            }
        };
        for g in gs {
            for a in g.atoms() {
                visit(a, &mut names, &mut atoms);
            }
        }
        loop {
            let next: Vec<Arc<Formula>> = if let Some(n) = names.pop() {
                self.syms.of(&n).cloned().collect()
            } else if let Some(a) = atoms.pop() {
                self.shared.get(&a).into_iter().flatten().cloned().collect()
            } else {
                break;
            };
            for g in next {
                if found.insert(g.clone()) {
                    for a in g.atoms() {
                        visit(a, &mut names, &mut atoms);
                    }
                }
            }
        }
        // The trees built again lose every node, so their counts go, and placing the conjuncts
        // counts them afresh.
        for g in gs.iter().chain(&found) {
            if let Some(b) = self.of_mut(g) {
                let r = self.find(b);
                self.others.remove(&r);
                self.gaps.remove(&r);
            }
        }
        for g in gs.iter().chain(&found) {
            if let Some(b) = self.put(g, &g.atoms(), None) {
                self.members.remove(&b);
                self.up.remove(&b);
                self.drop_node(b);
            }
            for a in g.atoms() {
                if let Atom::Sym(n) = a
                    && let Some(id) = self.name.remove(&n)
                {
                    self.up.remove(&id);
                    self.drop_node(id);
                }
            }
        }
        for g in &found {
            self.place(g);
        }
    }
}

/// The two names of `g` when it mentions two names and no other atom.
fn pair(g: &Formula) -> Option<[Arc<str>; 2]> {
    let mut atoms = g.atoms().into_iter();
    match (atoms.next(), atoms.next(), atoms.next()) {
        (Some(Atom::Sym(u)), Some(Atom::Sym(v)), None) => Some([u, v]),
        _ => None,
    }
}

/// A node of the graph of a block that [`Blocks::peel`] searches: a name, with its number, a
/// conjunct, or an atom other than a name, which links the conjuncts that mention it.
#[derive(Clone, Debug)]
enum Node {
    Name(Arc<str>, BlockId),
    Conj(Arc<Formula>),
    Atom(Atom),
}

/// What a search marks a [`Node`] by: a conjunct by its address, the one it has in every
/// index of a [`Blocks`]; a name by its number, on the side a path enters it (`In`) or the
/// side it leaves it (`Out`), so that a flow passes each name at most once.
// The address of a conjunct is a key only while the conjunct is alive, and no set or map keyed
// by `Key` is iterated: [`Search::seen`] holds each key's node (so its `Arc`) beside the key,
// [`Flow::seen`] gets a conjunct's key only in `Flow::reach`, which pushes the conjunct to
// `Flow::conjs` and the node to `Flow::queue`, and the map `at` of [`Blocks::peel`] is keyed
// by the nodes of `path`, which it holds for the whole peel. The three are read only by
// `get`, `contains` and `insert`, so their order reaches no answer. A conjunct has no id of its
// own to key by (`Formula::Con` carries none); one drawn by `fresh_id` would cost a field and
// a counter per conjunct for no change in what is found (PTR-keys-rest).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Key {
    In(BlockId),
    Out(BlockId),
    Conj(usize),
    Atom(Atom),
}

impl Node {
    /// The key of the node, a name's on the side a path leaves it.
    fn key(&self) -> Key {
        match self {
            Node::Name(_, id) => Key::Out(*id),
            Node::Conj(h) => Key::Conj(Arc::as_ptr(h) as *const () as usize),
            Node::Atom(a) => Key::Atom(a.clone()),
        }
    }
}

/// An iterator over a set of conjuncts held across the steps of a search, which reads the
/// blocks without changing them.
type Conjs<'a> = imbl::ordset::Iter<'a, Arc<Formula>, DefaultSharedPtr>;

/// The neighbors of a node not yet given: the conjuncts of a name in the block, or of an atom
/// other than a name (`true`: each is checked to lie in the block), not yet given, so that a
/// search can stop after any entry and go on; or the atoms of a conjunct.
// Complexity tradeoff: naive version, the cursor kept the last conjunct given and found the
// next by a range seek in the set, O(log n) comparisons of formulas per entry: on star_mixed,
// whose removals peel a block of all k disjunctions, the searches of `Blocks::peel` read
// near the whole block each time, and the seeks took 998M of 9,195M instructions at k = 512
// (10.7M of 967M at 64), the family's ratio at 8n 9.48 (PERF-l139-under9). Used: the set's
// iterator, held from one step to the next, O(log n) once and O(1) amortized per entry with no
// comparison; the searches read the blocks only through `&self`, so no set changes under it.
// The entries read are as many as before.
enum Cursor<'a> {
    Conjs(Option<Conjs<'a>>, bool),
    Atoms(Vec<Node>),
}

impl Blocks {
    /// A cursor over the neighbors of `n` in block `b`.
    fn cursor(&self, n: &Node, b: BlockId) -> Cursor<'_> {
        match n {
            Node::Name(x, _) => Cursor::Conjs(
                self.at.get(&b).and_then(|m| m.get(x)).map(OrdSet::iter),
                false,
            ),
            Node::Atom(a) => Cursor::Conjs(self.shared.get(a).map(OrdSet::iter), true),
            Node::Conj(h) => Cursor::Atoms(
                h.atoms()
                    .into_iter()
                    .map(|a| match a {
                        Atom::Sym(x) => {
                            let id = self.name[&x];
                            Node::Name(x, id)
                        }
                        a => Node::Atom(a),
                    })
                    .collect(),
            ),
        }
    }

    /// The next entry of `c`: `Some(Some(n))` for a neighbor in block `b`, `Some(None)` for a
    /// conjunct of another block, `None` when no entry is left. A name's entries are its
    /// conjuncts in `b` alone (`at`); an atom other than a name has all its conjuncts in one
    /// block.
    fn advance(&self, c: &mut Cursor<'_>, b: BlockId) -> Option<Option<Node>> {
        let (it, check) = match c {
            Cursor::Atoms(ns) => return ns.pop().map(Some),
            Cursor::Conjs(it, check) => (it.as_mut()?, *check),
        };
        let h = it.next()?.clone();
        Some((!check || self.of(&h) == Some(b)).then_some(Node::Conj(h)))
    }
}

/// One side of the search of [`Blocks::route`]: each node reached with the node it was
/// reached from.
struct Search<'a> {
    seen: HashMap<Key, (Node, Option<Key>)>,
    queue: VecDeque<Key>,
    cur: Option<(Key, Cursor<'a>)>,
}

impl<'a> Search<'a> {
    fn new(n: Node) -> Search<'a> {
        let k = n.key();
        Search {
            seen: HashMap::from([(k.clone(), (n, None))]),
            queue: VecDeque::from([k]),
            cur: None,
        }
    }

    /// Reads one entry: a neighbor in block `b` of the node being read, with that node's key.
    fn step(&mut self, blocks: &'a Blocks, b: BlockId) -> Option<(Key, Key, Node)> {
        let (k, c) = match &mut self.cur {
            Some(cur) => cur,
            None => {
                let k = self.queue.pop_front()?;
                let c = blocks.cursor(&self.seen[&k].0, b);
                self.cur.insert((k, c))
            }
        };
        match blocks.advance(c, b) {
            None => {
                self.cur = None;
                None
            }
            Some(None) => None,
            Some(Some(n)) => Some((k.clone(), n.key(), n)),
        }
    }

    /// The nodes from the one of key `k` back to where the search started.
    fn chain(&self, k: Key) -> Vec<Node> {
        let mut out = Vec::new();
        let mut at = Some(k);
        while let Some(k) = at {
            let (n, from) = &self.seen[&k];
            out.push(n.clone());
            at = from.clone();
        }
        out
    }
}

/// What a step of a [`Flow`] found.
enum Step {
    /// More is left to read.
    On,
    /// The search reached its end: a second path.
    Met,
    /// The search read all it can reach; the position on the path of the name it entered and
    /// could not leave.
    Out(usize),
}

/// A search of [`Blocks::peel`] for a second path from the name at `start` of the path `P`
/// to the one at `end`, sharing no name between them with the part of `P` from `start` to
/// `end`, in the residual graph of a flow of one along that part: a name of it between the
/// two may be left only on the side it was entered, `In`, after reaching it from its successor
/// on `P`, `Out`; a node of it may be reached back from its successor.
struct Flow<'a> {
    start: usize,
    end: usize,
    seen: HashSet<Key>,
    queue: VecDeque<(Key, Node)>,
    cur: Option<Cursor<'a>>,
    /// The conjuncts reached.
    conjs: Vec<Arc<Formula>>,
    /// The positions of the names between `start` and `end` entered.
    entered: Vec<usize>,
}

impl<'a> Flow<'a> {
    fn new(path: &[Node], start: usize, end: usize) -> Flow<'a> {
        let n = path[start].clone();
        Flow {
            start,
            end,
            seen: HashSet::from([n.key()]),
            queue: VecDeque::from([(n.key(), n)]),
            cur: None,
            conjs: Vec::new(),
            entered: Vec::new(),
        }
    }

    /// Whether position `i` lies strictly between `start` and `end`.
    fn inside(&self, i: usize) -> bool {
        self.start.min(self.end) < i && i < self.start.max(self.end)
    }

    /// The node before position `i` on the way from `start`, when `i` lies after `start` and
    /// not after `end`.
    fn before<'p>(&self, path: &'p [Node], i: usize) -> Option<&'p Node> {
        let (lo, hi) = (self.start.min(self.end), self.start.max(self.end));
        if i == self.start || i < lo || i > hi {
            return None;
        }
        Some(&path[if self.start < self.end { i - 1 } else { i + 1 }])
    }

    /// Marks `k` reached; whether it is the end.
    fn reach(&mut self, k: Key, n: Node, at: &HashMap<Key, usize>) -> bool {
        if let Key::In(id) = k
            && let Some(&i) = at.get(&Key::Out(id))
        {
            if i == self.end {
                return true;
            }
            if self.inside(i) && !self.seen.contains(&k) {
                self.entered.push(i);
            }
        }
        if self.seen.insert(k.clone()) {
            if let Node::Conj(h) = &n {
                self.conjs.push(h.clone());
            }
            self.queue.push_back((k, n));
        }
        false
    }

    /// Reads one entry within block `b`.
    fn step(
        &mut self,
        blocks: &'a Blocks,
        b: BlockId,
        path: &[Node],
        at: &HashMap<Key, usize>,
    ) -> Step {
        let c = match &mut self.cur {
            Some(c) => c,
            None => {
                let Some((k, n)) = self.queue.pop_front() else {
                    let out = self.entered.iter().copied().find(|&i| {
                        let Node::Name(_, id) = &path[i] else {
                            return false;
                        };
                        !self.seen.contains(&Key::Out(*id))
                    });
                    return Step::Out(out.expect("a search that runs out stops at a name of P"));
                };
                // The arcs of the flow's residual graph that are not edges of the block.
                let pos = |id: &BlockId| at.get(&Key::Out(*id)).copied();
                let mut extra: Vec<(Key, Node)> = Vec::new();
                match (&k, &n) {
                    (Key::Out(id), _) => {
                        if pos(id).is_some_and(|i| self.inside(i)) {
                            extra.push((Key::In(*id), n.clone()));
                        }
                    }
                    (Key::In(id), _) => {
                        if !pos(id).is_some_and(|i| self.inside(i)) {
                            extra.push((Key::Out(*id), n.clone()));
                        }
                        if let Some(p) = pos(id).and_then(|i| self.before(path, i)) {
                            extra.push((p.key(), p.clone()));
                        }
                    }
                    _ => {
                        if let Some(&i) = at.get(&k)
                            && let Some(p @ Node::Name(_, pid)) = self.before(path, i)
                        {
                            extra.push((Key::Out(*pid), p.clone()));
                        }
                    }
                }
                for (k, n) in extra {
                    if self.reach(k, n, at) {
                        return Step::Met;
                    }
                }
                if matches!(k, Key::In(_)) {
                    return Step::On;
                }
                self.cur.insert(blocks.cursor(&n, b))
            }
        };
        match blocks.advance(c, b) {
            None => self.cur = None,
            Some(None) => {}
            Some(Some(n)) => {
                let k = match &n {
                    Node::Name(_, id) => Key::In(*id),
                    n => n.key(),
                };
                if self.reach(k, n, at) {
                    return Step::Met;
                }
            }
        }
        Step::On
    }
}

/// One side of the walk of [`Blocks::bridge`] over a tree of the forest: the nodes reached,
/// a name with its text, and the one being read with its conjuncts not yet read ([`Cursor`]).
struct TreeWalk<'a> {
    seen: HashSet<BlockId>,
    nodes: Vec<(BlockId, Option<Arc<str>>)>,
    next: usize,
    cur: Option<(usize, Option<Conjs<'a>>)>,
}

impl<'a> TreeWalk<'a> {
    fn new((x, id): (&Arc<str>, BlockId)) -> TreeWalk<'a> {
        TreeWalk {
            seen: HashSet::from([id]),
            nodes: vec![(id, Some(x.clone()))],
            next: 0,
            cur: None,
        }
    }

    /// Reads one entry: a conjunct of a name, which gives its block, or a conjunct of a block,
    /// which gives its names. Whether anything was left to read.
    fn step(&mut self, blocks: &'a Blocks) -> bool {
        let (i, it) = match &mut self.cur {
            Some(cur) => cur,
            None => {
                if self.next == self.nodes.len() {
                    return false;
                }
                let (x, name) = &self.nodes[self.next];
                let set = match name {
                    Some(n) => blocks.syms.0.get(&**n),
                    None => blocks.members.get(x),
                };
                self.next += 1;
                self.cur.insert((self.next - 1, set.map(OrdSet::iter)))
            }
        };
        let Some(h) = it.as_mut().and_then(Iterator::next).cloned() else {
            self.cur = None;
            return true;
        };
        if self.nodes[*i].1.is_some() {
            let b = blocks
                .of(&h)
                .expect("a conjunct of the forest is in a block");
            if self.seen.insert(b) {
                self.nodes.push((b, None));
            }
        } else {
            for a in h.atoms() {
                if let Atom::Sym(n) = a {
                    let id = blocks.name[&n];
                    if self.seen.insert(id) {
                        self.nodes.push((id, Some(n)));
                    }
                }
            }
        }
        true
    }
}

/// Whether `f` is `false`.
fn is_false(f: &Formula) -> bool {
    matches!(f, Formula::Or(gs) if gs.is_empty())
}

impl fmt::Display for Conjuncts {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.formula())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn row(terms: &[(&str, i64)], c: i64, rel: Rel) -> Formula {
        let lin = terms.iter().fold(Lin::constant(c), |l, (n, k)| {
            l.plus(&Lin::atom(Atom::Sym((*n).into())).times(*k))
        });
        Formula::Con(Con { lin, rel })
    }

    /// `Rows::ends` gives the conjuncts that are no rows and, of each key, exactly the rows of
    /// least and greatest `b`, also with the middle rows added after the ends and after the
    /// greatest row is removed (row TEST-hub-bounds-extreme-row-mutation). The scope-level test
    /// `l01_39_reduced_product::scaling::hub_bounds_match_the_full_core_after_rows_among_the_
    /// hubs` cannot tell a wrong end from the right one: every row of a key `(x, y, a, c)` passes
    /// through `(-c/a, 0)`, so no case has rows of one key that do not meet at one point, and
    /// each new row is projected exactly when it is assumed, whatever `ends` gives later. So
    /// `ends` is checked here: reading the second-greatest row in place of the greatest, when a
    /// key has more than two rows, fails this test at `k = 2` (run once, not kept).
    #[test]
    fn rows_ends_are_the_rows_of_least_and_greatest_b_of_each_key() {
        let arc = |g: Formula| Arc::new(g);
        let x_jy = |j: i64| arc(row(&[("x", 1), ("y", j)], -1, Rel::Ge));
        let x_jz = |j: i64| arc(row(&[("x", 2), ("z", j)], 3, Rel::Ge));
        let other = arc(row(&[("x", 1), ("y", 1), ("z", 1)], 0, Rel::Ge));
        for k in 2..=5i64 {
            let mut rows = Rows::default();
            rows.insert(&other);
            // The ends first, then the middle rows, and a second key of two rows.
            for j in [k, -k].into_iter().chain((1..k).flat_map(|j| [j, -j])) {
                rows.insert(&x_jy(j));
            }
            rows.insert(&x_jz(-1));
            rows.insert(&x_jz(4));
            let ends = |rows: &Rows| {
                let mut e: Vec<Arc<Formula>> = rows.ends().cloned().collect();
                e.sort();
                e
            };
            let want = |hi: i64| {
                let mut w = vec![other.clone(), x_jy(-k), x_jy(hi), x_jz(-1), x_jz(4)];
                w.sort();
                w
            };
            assert_eq!(ends(&rows), want(k), "k = {k}");
            rows.remove(&x_jy(k));
            assert_eq!(ends(&rows), want(k - 1), "k = {k}, greatest removed");
        }
    }

    /// `add_with` and `remove_with` through one `Last` give the sets plain `add` and `remove`
    /// give, step by step, over adds and removes of present and absent values, a set emptied
    /// and a name with no set; and two names given the same values in turn share one set.
    #[test]
    fn uses_through_the_last_change_equal_plain_uses() {
        let names: Vec<Arc<str>> = ["x", "y", "z"].iter().map(|n| Arc::from(*n)).collect();
        let mut with = Uses::<u32>::default();
        let mut plain = Uses::<u32>::default();
        let mut last = Last::default();
        // A fixed linear congruential sequence, so the run is the same each time.
        let mut s: u64 = 12345;
        for step in 0..4000 {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let t = ((s >> 33) % 7) as u32;
            let add = (s >> 40) % 3 != 0;
            // Mostly the same value at x then y, as an index of a conjunct's names gives it.
            let at: Vec<&Arc<str>> = if (s >> 45) % 4 == 0 {
                vec![&names[2]]
            } else {
                vec![&names[0], &names[1]]
            };
            for n in at {
                if add {
                    with.add_with(n, &t, &mut last);
                    plain.add(n, &t);
                } else {
                    with.remove_with(n, &t, &mut last);
                    plain.remove(n, &t);
                }
                assert_eq!(
                    with,
                    plain,
                    "step {step}: {} {t} at {n}",
                    if add { "add" } else { "remove" }
                );
            }
        }
        let mut shared = Uses::<u32>::default();
        let mut last = Last::default();
        for t in 0..50 {
            shared.add_with(&names[0], &t, &mut last);
            shared.add_with(&names[1], &t, &mut last);
        }
        assert!(shared.set("x").unwrap().ptr_eq(shared.set("y").unwrap()));
        assert_eq!(shared.count("x"), 50);
    }

    #[test]
    fn reach_eqs_matches_reach_with_is_eq_filter() {
        let mut r1 = Conjuncts::default();
        let mut r2 = Conjuncts::default();
        let e1 = row(&[("x", 1), ("y", -1)], 0, Rel::Eq);
        let e2 = row(&[("y", 1), ("z", -2)], 1, Rel::Eq);
        let e3 = row(&[("a", 1), ("b", -1)], 0, Rel::Eq);
        let g1 = row(&[("x", 1), ("w", 1)], -1, Rel::Ge);
        let d1 = Formula::or(vec![
            row(&[("x", 1), ("y", 1), ("w", 1)], -1, Rel::Ge),
            row(&[("x", 1), ("y", -1), ("v", 1)], -1, Rel::Ge),
        ]);
        r1.and(e1.clone());
        r1.and(g1.clone());
        r1.and(d1.clone());
        r2.and(e2.clone());
        r2.and(e3.clone());
        r2.and(d1.clone());
        let is_eq = |g: &Formula| matches!(g, Formula::Con(c) if c.rel == Rel::Eq);
        for seed in ["x", "z", "a", "w", "v"] {
            let got = reach_eqs(&[&r1, &r2], [Arc::<str>::from(seed)]);
            let want = reach(&[&r1, &r2], [Arc::<str>::from(seed)], is_eq);
            assert_eq!(got, want, "seed {seed}");
        }
        r1.remove(&Arc::new(e1));
        for seed in ["x", "y", "z"] {
            let got = reach_eqs(&[&r1, &r2], [Arc::<str>::from(seed)]);
            let want = reach(&[&r1, &r2], [Arc::<str>::from(seed)], is_eq);
            assert_eq!(got, want, "after remove, seed {seed}");
        }
    }

    #[test]
    fn remove_covered_keeps_the_same_block_partition_as_from_scratch() {
        let mut rel = Conjuncts::default();
        let mut expected: Vec<Formula> = Vec::new();
        for j in 1..=6i64 {
            let d = Formula::or(vec![
                row(&[("x", 1), ("y", j), ("w", 1)], -1, Rel::Ge),
                row(&[("x", 1), ("y", -j), ("v", 1)], -1, Rel::Ge),
            ]);
            rel.and(d.clone());
            expected.push(d);
        }
        // Add 3-name constraints covered by the 4-name disjunctions, then swap them out.
        let c1 = row(&[("x", 1), ("y", 7), ("w", 1)], -1, Rel::Ge);
        let c2 = row(&[("x", 1), ("y", -7), ("v", 1)], -1, Rel::Ge);
        let d7 = Formula::or(vec![c1.clone(), c2.clone()]);
        rel.and(c1.clone());
        rel.and(c2.clone());
        rel.swap(&[Arc::new(c1), Arc::new(c2)], d7.clone());
        expected.push(d7);

        let mut fresh = Conjuncts::default();
        for f in expected {
            fresh.and(f);
        }
        let parts = |c: &Conjuncts| -> BTreeSet<BTreeSet<Arc<Formula>>> {
            c.blocks()
                .members
                .values()
                .map(|ms| ms.iter().cloned().collect())
                .collect()
        };
        assert_eq!(parts(&rel), parts(&fresh));
    }

    /// Two conjuncts of the pair `a`, `b` in one block, added in order or in reverse: the
    /// pair's count is checked by [`Blocks::well_formed`] (the block's pair counts taken away
    /// are caught), and taking one of the two away keeps the block and the other's place
    /// (cross-review R1-CODEX, Q3).
    #[test]
    fn a_pair_held_twice_keeps_its_block_when_one_is_taken_away() {
        let edge = |a, b, c| Arc::new(row(&[(a, 1), (b, -1)], c, Rel::Ge));
        let gs = [
            edge("a", "b", 0),
            edge("a", "c", 0),
            edge("b", "c", 0),
            edge("a", "b", 1),
        ];
        for order in [[0, 1, 2, 3], [3, 2, 1, 0]] {
            let mut blocks = Blocks::default();
            for i in order {
                blocks.add(&gs[i]);
                assert_eq!(blocks.well_formed(), Ok(()), "order {order:?}");
            }
            let b = blocks.of(&gs[0]).expect("the block of the first conjunct");
            assert_eq!(blocks.members(b).count(), 4);
            let mut broken = blocks.clone();
            broken.pairs.remove(&b);
            assert_eq!(
                broken.well_formed(),
                Err("the counts of the pairs of the blocks are not those of the blocks".into())
            );
            blocks.remove(&gs[0..1]);
            assert_eq!(blocks.well_formed(), Ok(()), "order {order:?}");
            assert_eq!(blocks.members(b).count(), 3);
            assert_eq!(blocks.of(&gs[3]), Some(b));
        }
    }

    /// A conjunct held in a block but listed in none is caught by [`Blocks::well_formed`]
    /// (cross-review R1-CODEX-01): the members only check `of` one way.
    #[test]
    fn well_formed_refuses_a_conjunct_held_in_no_block() {
        let mut blocks = Blocks::default();
        let g = Arc::new(row(&[("x", 1), ("y", -1)], 0, Rel::Ge));
        blocks.add(&g);
        assert_eq!(blocks.well_formed(), Ok(()));
        let stray = Arc::new(row(&[("u", 1)], -1, Rel::Ge));
        let b = blocks.of(&g).expect("the block of the conjunct added");
        blocks.of.insert(stray, b);
        assert_eq!(
            blocks.well_formed(),
            Err("the conjuncts with a block are not those of the blocks".to_string())
        );
    }

    fn diff(a: &str, b: &str, c: i64) -> Formula {
        row(&[(a, 1), (b, -1)], c, Rel::Ge)
    }

    fn block_partition(c: &Conjuncts) -> BTreeSet<BTreeSet<Arc<Formula>>> {
        c.blocks()
            .all()
            .map(|b| c.blocks().members(b).cloned().collect())
            .collect()
    }

    #[test]
    fn balanced_binary_merge_tree_is_well_formed_and_order_independent() {
        // Adversarial Q5 workload: 2^k disjoint 3-cycles merged pairwise in k balanced rounds so
        // equal-sized blocks merge at every level.
        let k = 5usize; // 32 leaves -> 1 block of 32*3 + 31*2 = 158 conjuncts, 96 names.
        let leaves = 1usize << k;
        let mut ordered: Vec<Formula> = Vec::new();
        for i in 0..leaves {
            let a = format!("n_{i}_0");
            let b = format!("n_{i}_1");
            let c = format!("n_{i}_2");
            ordered.push(diff(&a, &b, 0));
            ordered.push(diff(&b, &c, 0));
            ordered.push(diff(&c, &a, 0));
        }
        let mut step = 1usize;
        while step < leaves {
            for base in (0..leaves).step_by(step * 2) {
                let l0 = format!("n_{base}_0");
                let r0 = format!("n_{}_0", base + step);
                let l1 = format!("n_{base}_1");
                let r1 = format!("n_{}_1", base + step);
                ordered.push(diff(&l0, &r0, 0));
                ordered.push(diff(&r1, &l1, 0));
            }
            step *= 2;
        }

        let mut fwd = Conjuncts::default();
        for f in &ordered {
            fwd.and(f.clone());
        }
        fwd.blocks().well_formed().expect("forward well-formed");
        assert!(!fwd.blocks().uf.is_empty(), "balanced merges populated uf");
        assert_eq!(fwd.blocks().all().count(), 1);
        let root = fwd.blocks().all().next().expect("one block");
        let names_fwd: Vec<Arc<str>> = fwd.blocks().names_of(root).cloned().collect();
        assert_eq!(names_fwd.len(), leaves * 3);
        assert!(names_fwd.windows(2).all(|w| w[0] < w[1]));
        for n in &names_fwd {
            let mb: Vec<BlockId> = fwd.blocks().moving_blocks(n).collect();
            assert_eq!(mb, vec![root]);
        }

        // Reverse order and deterministic stride order must yield the exact same block partition.
        let mut rev = Conjuncts::default();
        for f in ordered.iter().rev() {
            rev.and(f.clone());
        }
        rev.blocks().well_formed().expect("reverse well-formed");
        assert_eq!(block_partition(&fwd), block_partition(&rev));

        let mut permuted = Conjuncts::default();
        let n = ordered.len();
        let mut idx = 0usize;
        for _ in 0..n {
            permuted.and(ordered[idx].clone());
            idx = (idx + 37) % n; // gcd(37, 158) == 1
        }
        permuted
            .blocks()
            .well_formed()
            .expect("permuted well-formed");
        assert_eq!(block_partition(&fwd), block_partition(&permuted));
    }

    #[test]
    fn shrink_then_merge_chain_keeps_uf_rank_logarithmic() {
        // Adversarial Q5 workload against naive size-based aliasing: maintain a live block of
        // size 2 on (u, v), merge it into a fresh block of size 3 on (u_next, v_next) so the old
        // block is always absorbed into the new one, then shrink the winner back to size 2.
        // Without union-by-rank, `uf` chains grow to length 48; with union-by-rank, depth <= 7.
        let mut b = Blocks::default();
        let mut u = String::from("u_0");
        let mut v = String::from("v_0");
        let mut cur_edges = vec![Arc::new(diff(&u, &v, 0)), Arc::new(diff(&u, &v, 1))];
        for e in &cur_edges {
            b.add(e);
        }

        for round in 1..=48usize {
            let u_next = format!("u_{round}");
            let v_next = format!("v_{round}");
            let n0 = Arc::new(diff(&u_next, &v_next, 0));
            let n1 = Arc::new(diff(&u_next, &v_next, 1));
            let n2 = Arc::new(diff(&u_next, &v_next, 2));
            b.add(&n0);
            b.add(&n1);
            b.add(&n2);
            let big_id = b.of(&n0).expect("big block");
            let prev_id = b.of(&cur_edges[0]).expect("prev block");
            assert_ne!(big_id, prev_id);

            let br1 = Arc::new(diff(&u, &u_next, 0));
            let br2 = Arc::new(diff(&v, &v_next, 0));
            b.add(&br1);
            b.add(&br2);
            // `big_id` had 3 conjuncts > `prev_id`'s 2, so `prev_id` was merged into `big_id`.
            assert_eq!(b.of(&cur_edges[0]), Some(big_id));
            assert_eq!(b.of(&n0), Some(big_id));

            // Remove old edges and one edge of `big_id`, leaving `big_id` alive with 2 conjuncts.
            let mut drop_list = vec![br2, br1, n2];
            drop_list.extend(cur_edges);
            b.remove(&drop_list);
            b.well_formed()
                .expect("well-formed after shrink-then-merge");
            assert_eq!(b.of(&n0), Some(big_id));

            cur_edges = vec![n0, n1];
            u = u_next;
            v = v_next;
        }
        assert!(b.uf.len() >= 48, "expected >= 48 merged blocks in uf");
        let mut max_depth = 0usize;
        for (&id, _) in &b.uf {
            let mut cur = id;
            let mut depth = 0usize;
            while let Some(&node) = b.uf.get(&cur) {
                match node {
                    UfNode::Root { .. } => break,
                    UfNode::Parent(p) => {
                        depth += 1;
                        cur = p;
                    }
                }
            }
            max_depth = max_depth.max(depth);
        }
        assert!(
            max_depth <= 8,
            "uf max depth {max_depth} grew beyond log2 bound"
        );
    }

    #[test]
    fn branched_clones_and_mutations_stay_independent_and_well_formed() {
        let mut base = Conjuncts::default();
        let e0 = diff("a", "b", 0);
        let e1 = diff("b", "c", 0);
        let e2 = diff("c", "d", 0);
        for f in [&e0, &e1, &e2] {
            base.and(f.clone());
        }
        let snapshot = base.blocks().clone();
        let old_b = snapshot.of(&Arc::new(e0.clone())).expect("e0 placed");

        let mut left = base.clone();
        let mut right = base.clone();

        // Left branch closes cycle a-b-c-a, hangs a conjunct, then peels/removes.
        let l_close = diff("c", "a", 0);
        left.and(l_close.clone());
        left.blocks().well_formed().expect("left after cycle");
        let left_now = left.blocks().now_of(&snapshot, old_b);
        assert_eq!(left_now.len(), 1);
        let merged_block = *left_now.iter().next().expect("merged block");
        assert_eq!(
            left.blocks().moving_blocks("b").collect::<Vec<_>>(),
            vec![merged_block]
        );
        left.remove(&Arc::new(l_close));
        left.blocks().well_formed().expect("left after peel");

        // Right branch closes a different cycle b-c-d-b and replaces an edge.
        let r_close = diff("d", "b", 0);
        right.and(r_close);
        right.blocks().well_formed().expect("right after cycle");
        let r_repl = diff("b", "c", 5);
        right.blocks.replace(&Arc::new(e1), &Arc::new(r_repl));
        right.blocks().well_formed().expect("right after replace");

        // Base snapshot must be untouched.
        snapshot.well_formed().expect("snapshot still well-formed");
        assert_eq!(snapshot.all().count(), 3);
    }

    #[test]
    fn merge_with_product_atoms_and_hung_conjuncts_preserves_all_indexes() {
        let mut b = Blocks::default();
        let prod = Atom::Product(Factor::Sym(Arc::from("p")), Factor::Sym(Arc::from("q")));
        let g1 = Arc::new(Formula::Con(Con {
            lin: Lin::atom(Atom::Sym(Arc::from("a")))
                .plus(&Lin::atom(prod.clone()))
                .plus(&Lin::constant(0)),
            rel: Rel::Ge,
        }));
        let g2 = Arc::new(Formula::Con(Con {
            lin: Lin::atom(Atom::Sym(Arc::from("b")))
                .plus(&Lin::atom(prod))
                .plus(&Lin::constant(1)),
            rel: Rel::Ge,
        }));
        let g3 = Arc::new(diff("a", "c", 0));
        let g4 = Arc::new(diff("b", "d", 0));
        b.add(&g1);
        b.add(&g3);
        // Hang g1 at "p" and "a" before cross-tree merge with g2.
        b.hang(&Arc::from("p"), &g1, true);
        b.hang(&Arc::from("a"), &g1, true);
        b.well_formed().expect("before product merge");

        b.add(&g4);
        b.add(&g2); // shares Atom::Product("p","q") with g1 across trees -> cross-tree merge!
        b.well_formed().expect("after product merge");
        assert_eq!(b.of(&g1), b.of(&g2));
        // "p" is mentioned by both g1 (hung) and g2 (moving), so moving_blocks("p") has the block.
        let merged = b.of(&g1).expect("g1 in merged block");
        assert_eq!(b.moving_blocks("p").collect::<Vec<_>>(), vec![merged]);
        // Unhang g1 at "p" and "a" after merge; tags must still resolve cleanly.
        b.hang(&Arc::from("p"), &g1, false);
        b.hang(&Arc::from("a"), &g1, false);
        b.well_formed().expect("after post-merge unhang");
        // Verify moving_blocks("a") is sorted ascending and has both `merged` and `g3`'s block.
        let mb_a: Vec<BlockId> = b.moving_blocks("a").collect();
        assert_eq!(mb_a.len(), 2);
        assert!(mb_a[0] < mb_a[1]);
        // Remove g1 and verify rebuild/split leaves indexes well-formed.
        b.remove(&[g1]);
        b.well_formed().expect("after removing product conjunct");
    }

    #[test]
    fn well_formed_negative_controls_detect_corrupted_indexes() {
        let mut b = Blocks::default();
        let g1 = Arc::new(diff("x", "y", 0));
        let g2 = Arc::new(diff("y", "z", 0));
        let g3 = Arc::new(diff("z", "x", 0));
        b.add(&g1);
        b.add(&g2);
        b.add(&g3);
        b.well_formed().expect("clean baseline");

        // Negative control 1: stale `of` entry not in `members`.
        let mut stale_of = b.clone();
        let ghost = Arc::new(diff("u", "v", 0));
        stale_of.of.insert(ghost, 999);
        assert!(stale_of.well_formed().is_err(), "stale `of` must fail");

        // Negative control 2: mismatched `moving_at` tag relative to `names_in`.
        let mut bad_tag = b.clone();
        let live = bad_tag.of(&g1).expect("g1 block");
        if let Some(m) = bad_tag.moving_at.get_mut("x") {
            m.clear();
            m.insert(live + 10_000, 2);
        }
        assert!(
            bad_tag.well_formed().is_err(),
            "bad `moving_at` tag must fail"
        );

        // Negative control 3: cycle in `uf`.
        let mut uf_cycle = b.clone();
        uf_cycle.uf.insert(500, UfNode::Parent(501));
        uf_cycle.uf.insert(501, UfNode::Parent(500));
        assert!(uf_cycle.well_formed().is_err(), "`uf` cycle must fail");
    }
}
