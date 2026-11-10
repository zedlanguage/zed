//! The linear relation of a scope (step L1.39) as a persistent set of conjuncts, with the
//! conjuncts that mention each name, of the constraints on each term the tighter one, and of
//! the disjunctions of two constraints on each pair of terms those that no other implies.
//!
//! A scope is copied for each case of a test and the cases are joined, so the relation is held
//! in persistent maps: a copy costs O(1), a new conjunct O(log n) in the size of the relation,
//! and two relations made from one by a few changes are compared, and their differing
//! conjuncts found, in time near the number of changes. The conjuncts are in the order of
//! formulas, so a relation does not depend on the order its conjuncts were added in.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;
use std::ops::{Bound, RangeBounds};
use std::sync::Arc;

use imbl::{OrdMap, OrdSet};

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
    pub fn add(&mut self, name: &Arc<str>, t: &T) {
        self.0.entry(name.clone()).or_default().insert(t.clone());
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

/// The key of a constraint for the rule that keeps the tighter of two: its term and relation.
type Tight = (BTreeMap<Atom, Int>, Rel);

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
    /// Of the constraints on each term with each relation, the one kept.
    tight: OrdMap<Tight, Arc<Formula>>,
    /// Of the disjunctions of two constraints on each pair of terms, those that no other
    /// implies ([`Conjuncts::pair`]).
    pairs: OrdMap<PairKey, Front>,
    /// The conjuncts that mention each name, alone or in a product.
    users: Uses<Arc<Formula>>,
    /// The blocks of the conjuncts: the forest of the conjuncts of no star, and each star's
    /// conjuncts as a block of its own outside it ([`Blocks::detach`]).
    blocks: Blocks,
    /// The stars and what keeps them current, apart so that a conjunction is small to move.
    index: Box<StarIndex>,
}

/// Two names, in order.
type NamePair = (Arc<str>, Arc<str>);

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

/// The stars of a conjunction ([`Conjuncts::star`]) and the indexes that keep them current.
#[derive(Clone, Debug, Default)]
struct StarIndex {
    /// The names of the shape of a leaf ([`Conjuncts::star`]), each with its shape.
    shapes: OrdMap<Arc<str>, Arc<Shape>>,
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
    /// Of each name, the other names of its `free` conjuncts of two names, each with how many
    /// mention it: of a satellite ([`Conjuncts::star`]), the names it relates to.
    ties: OrdMap<Arc<str>, OrdMap<Arc<str>, usize>>,
    /// Of each name, how many of its `free` conjuncts are of other than two names: a name
    /// with none is a satellite.
    wide: OrdMap<Arc<str>, usize>,
    /// The other names each hub's `free` conjuncts mention, each with how many mention it;
    /// kept only at the hubs of `level`, so that a conjunct of many names costs no more than
    /// its names unless they are such hubs.
    near: OrdMap<Arc<str>, OrdMap<Arc<str>, usize>>,
    /// Of each name, the hubs whose `near` holds it.
    nearby: Uses<Arc<str>>,
    /// Of each satellite related to a hub it is near, one such hub: the one that needs the
    /// names the satellite relates to, while each other hub it is near needs this one
    /// ([`StarIndex::place`]).
    anchor: OrdMap<Arc<str>, Arc<str>>,
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
    /// The conjuncts of the stars at each hub.
    hangs: Uses<Arc<Formula>>,
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
    needs: OrdMap<Arc<str>, OrdMap<Arc<str>, usize>>,
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
    /// `l01_39_reduced_product::linked::a_satellite_of_every_hub_costs_its_related_names_once`
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
/// (Shostak's node `z`), so that a bound is an edge to or from it.
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
    let mut out = BTreeSet::new();
    for a in f.atoms() {
        match a {
            Atom::Sym(n) => {
                out.insert(n);
            }
            Atom::Product(x, y) => {
                for f in [x, y] {
                    if let Factor::Sym(n) = f {
                        out.insert(n);
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
    /// or a disjunction of such constraints, such as `x < n || x < m`, which holds for `x` far
    /// enough on the side each of its constraints does;
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

    /// The leaves of the stars of class `c`.
    pub fn class_leaves(&self, c: &Class) -> impl Iterator<Item = &Arc<str>> {
        self.index.classes.get(c).into_iter().flatten()
    }

    /// The classes of the stars of two hubs or more of which `h` is a hub.
    pub fn classes_at(&self, h: &str) -> impl Iterator<Item = &Class> {
        self.index.class_at.of(h)
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
        self.index.hangs.of(y)
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
        let mut witness: Option<(&Arc<str>, &Arc<Formula>)> = None;
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
                if c.rel != Rel::Ge || c.lin.terms.keys().any(|a| !matches!(a, Atom::Sym(_))) {
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
                        unreachable!("a conjunct of names alone")
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
                    if witness.is_none() && self.users.count(h) <= count {
                        witness = Some((h, g));
                    }
                }
                if c.lin.terms.len() == 1 {
                    return Err(why(vec![g.clone()]));
                }
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
        if let Some((h, g)) = witness {
            return Err(Why {
                count: Some(h.clone()),
                ..why(vec![g.clone()])
            });
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
            for h in &ns {
                let want = self.users.has(h, &g)
                    && !self.index.owned.has(h, &g)
                    && !self.index.solo.has(h, &g);
                if want == self.index.free.has(h, &g) {
                    continue;
                }
                if want {
                    self.index.free.add(h, &g);
                } else {
                    self.index.free.remove(h, &g);
                }
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
                        self.index.hangs.remove(&h, g);
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
                    self.index.hangs.add(&h, g);
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

    /// The conjunction without the conjuncts `gone` and with `f`, in time near theirs: `f` is
    /// added before `gone` leave the blocks, and a conjunct of `f` of the same atoms as one of
    /// `gone` takes its place in its block ([`Blocks::replace`]). So the join of two cases that
    /// differ in a conjunct of a chain replaces it, where removing it first would cut the chain
    /// and build the blocks of the rest again.
    pub fn swap(&mut self, gone: &[Arc<Formula>], f: Formula) {
        let mut held = Held::new();
        let mut p = Pending::default();
        for g in gone {
            if self.unindex(g, &mut p) {
                held.entry(g.atoms()).or_default().push(g.clone());
            }
        }
        self.and_held(f, &mut held, &mut p);
        self.flush(p);
        let rest: Vec<Arc<Formula>> = held.into_values().flatten().collect();
        self.unplace(&rest);
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
        let mut looser = None;
        if let Formula::Con(c) = &g
            && let Some(old) = self.tight.get(&(c.lin.terms.clone(), c.rel))
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
        for n in &ns {
            self.users.add(n, &g);
            self.index.moving.add(n, &g);
        }
        if let Some(n) = alone(&g) {
            self.index.solo.add(&n, &g);
        }
        if let Formula::Con(c) = &*g {
            self.tight.insert((c.lin.terms.clone(), c.rel), g.clone());
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
        self.pairs.entry(key).or_default().insert(c, (d, g.clone()));
        true
    }

    /// Removes `g` from the set and from every index but the blocks; whether it was there.
    /// A star that held it is changed by [`Conjuncts::flush`].
    fn unindex(&mut self, g: &Arc<Formula>, p: &mut Pending) -> bool {
        if self.set.remove(g).is_none() {
            return false;
        }
        let ns = names(g);
        for n in &ns {
            self.users.remove(n, g);
            self.index.moving.remove(n, g);
        }
        if let Some(n) = alone(g) {
            self.index.solo.remove(&n, g);
        }
        self.counted(g, &ns, false, p);
        if let Formula::Con(c) = &**g {
            let key = (c.lin.terms.clone(), c.rel);
            if self.tight.get(&key) == Some(g) {
                self.tight.remove(&key);
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

/// The conjuncts of `rels` linked to `seeds` by chains of conjuncts that share a name, only
/// conjuncts `follow` keeps taken, and the names they mention with the seeds: a search from
/// the seeds with a visited set, in time near the conjuncts found.
pub fn reach(
    rels: &[&Conjuncts],
    seeds: impl IntoIterator<Item = Arc<str>>,
    follow: impl Fn(&Formula) -> bool,
) -> (BTreeSet<Arc<Formula>>, BTreeSet<Arc<str>>) {
    let mut found: BTreeSet<Arc<Formula>> = BTreeSet::new();
    let mut seen: BTreeSet<Arc<str>> = BTreeSet::new();
    let mut work: Vec<Arc<str>> = Vec::new();
    for n in seeds {
        if seen.insert(n.clone()) {
            work.push(n);
        }
    }
    while let Some(n) = work.pop() {
        for g in rels.iter().flat_map(|r| r.users.of(&n)) {
            if !follow(g) || found.contains(g) {
                continue;
            }
            found.insert(g.clone());
            for m in names(g) {
                if seen.insert(m.clone()) {
                    work.push(m);
                }
            }
        }
    }
    (found, seen)
}

/// A block of a [`Blocks`] forest, or a name in it.
pub type BlockId = u64;

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
/// merged into one, the smaller blocks' conjuncts moved into the largest (so a conjunct is
/// moved O(log n) times): with the persistent maps, O(log² n) amortized per conjunct. A
/// removed conjunct of two names and no other atom is taken out in time near the smaller
/// side of each split it makes, searched from both of its names in turn (`Blocks::cut`). Any
/// other removed conjunct that is a block alone and shares at most one name with the rest is
/// unlinked in O(log n); a removal from a block of names whose other conjuncts still link all
/// its names places those conjuncts again, in time near the block (`Blocks::split`); any
/// other removal rebuilds the blocks of the conjuncts linked to it, in time near their number.
/// The blocks do not depend on the order the conjuncts came in; the roots and the numbers do,
/// and nothing reads them but this forest.
#[derive(Clone, Debug, Default)]
pub struct Blocks {
    /// The next number for a block or a name.
    next: BlockId,
    /// Each name's number.
    name: OrdMap<Arc<str>, BlockId>,
    /// Each conjunct's block.
    of: OrdMap<Arc<Formula>, BlockId>,
    /// Each block's conjuncts.
    members: OrdMap<BlockId, OrdSet<Arc<Formula>>>,
    /// Each node's parent in its tree; a root has none.
    up: OrdMap<BlockId, BlockId>,
    /// The tree of each node of the forest: a number of its own, never a node's.
    tree_of: OrdMap<BlockId, BlockId>,
    /// The nodes of each tree.
    trees: OrdMap<BlockId, OrdSet<BlockId>>,
    /// The conjuncts that mention each name as an atom of its own.
    syms: Uses<Arc<Formula>>,
    /// The conjuncts of each block that mention each name, the entries of `syms` cut by `of`;
    /// none empty.
    // Complexity tradeoff: the searches of `Blocks::cut` could read a name's conjuncts from
    // `syms` and skip those of other blocks, O(1) to keep but O(d) per name read for a name
    // of d conjuncts in all blocks, so a removal beside a name of many blocks cost near d and
    // d such removals O(d²). This index gives a name's conjuncts in one block, so a search
    // reads only the block's; it costs O(log n) per name of a conjunct each time the
    // conjunct changes block, the order those moves already cost, and one entry per name of
    // each conjunct.
    at: OrdMap<(Arc<str>, BlockId), OrdSet<Arc<Formula>>>,
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
}

/// Adds `by` to the count of `r` in `counts`, which holds no zero.
fn tally(counts: &mut OrdMap<BlockId, usize>, r: BlockId, by: isize) {
    let n = counts.get(&r).copied().unwrap_or(0).checked_add_signed(by);
    debug_assert!(n.is_some(), "a count of a tree below zero");
    let n = n.unwrap_or(0);
    if n == 0 {
        counts.remove(&r);
    } else {
        counts.insert(r, n);
    }
}

impl Blocks {
    /// The block of `g`.
    pub fn of(&self, g: &Arc<Formula>) -> Option<BlockId> {
        self.of.get(g).copied()
    }

    /// The conjuncts of block `b`.
    pub fn members(&self, b: BlockId) -> impl Iterator<Item = &Arc<Formula>> {
        self.members.get(&b).into_iter().flatten()
    }

    /// The conjuncts of block `b` as their persistent set ([`Uses::set`]).
    pub fn member_set(&self, b: BlockId) -> Option<&OrdSet<Arc<Formula>>> {
        self.members.get(&b)
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
        let mut ms = OrdSet::new();
        for g in gs {
            let was = self.put(&g, &g.atoms(), Some(b));
            debug_assert!(was.is_none(), "a conjunct detached is in no block");
            ms.insert(g);
        }
        self.members.insert(b, ms);
        self.apart.insert(b);
        b
    }

    /// Removes the block `b` made by [`Blocks::detach`].
    pub fn undetach(&mut self, b: BlockId) {
        let removed = self.apart.remove(&b);
        debug_assert!(removed.is_some(), "a block apart from the forest");
        for g in self.members.remove(&b).into_iter().flatten() {
            self.put(&g, &g.atoms(), None);
        }
    }

    /// Puts `g`, of the atoms `atoms`, in block `to`, or in none, and gives the block it was
    /// in; `of` and `at` change together. In O(log n) per name of `g`.
    fn put(
        &mut self,
        g: &Arc<Formula>,
        atoms: &BTreeSet<Atom>,
        to: Option<BlockId>,
    ) -> Option<BlockId> {
        let was = match to {
            Some(b) => self.of.insert(g.clone(), b),
            None => self.of.remove(g),
        };
        if was == to {
            return was;
        }
        for a in atoms {
            let Atom::Sym(x) = a else {
                continue;
            };
            if let Some(w) = was {
                let key = (x.clone(), w);
                if let Some(set) = self.at.get_mut(&key) {
                    set.remove(g);
                    if set.is_empty() {
                        self.at.remove(&key);
                    }
                }
            }
            if let Some(t) = to {
                self.at.entry((x.clone(), t)).or_default().insert(g.clone());
            }
        }
        was
    }

    fn fresh(&mut self) -> BlockId {
        self.next += 1;
        self.next
    }

    /// Checks the forest, for tests: each conjunct of the forest is in the block that holds
    /// it, conjuncts that share an atom other than a name are in one block, each name is
    /// mentioned, and each name's conjuncts by block are those of the blocks; the parent
    /// links are exactly the pairs of a block and a name it mentions, each tree has one root
    /// that every node's links lead to, and the labels of the trees are those links'
    /// components; each tree's counts are those of its conjuncts and names.
    /// In time near the forest's size times its depth.
    pub fn well_formed(&self) -> Result<(), String> {
        let mut nodes: BTreeSet<BlockId> = BTreeSet::new();
        let mut names_of: BTreeMap<BlockId, BTreeSet<BlockId>> = BTreeMap::new();
        let mut others: BTreeMap<BlockId, usize> = BTreeMap::new();
        let mut gaps: BTreeMap<BlockId, usize> = BTreeMap::new();
        let mut at: BTreeMap<(Arc<str>, BlockId), BTreeSet<Arc<Formula>>> = BTreeMap::new();
        for (&b, ms) in &self.members {
            for h in ms {
                if self.of.get(h) != Some(&b) {
                    return Err(format!("{h} is in block {b} but not held there"));
                }
                for a in h.atoms() {
                    if let Atom::Sym(x) = a {
                        at.entry((x, b)).or_default().insert(h.clone());
                    }
                }
            }
            if self.apart.contains(&b) {
                if self.tree_of.contains_key(&b) || self.up.contains_key(&b) {
                    return Err(format!("block {b} apart from the forest is in a tree"));
                }
                continue;
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
                            if let Some(o) = gs.map(|o| self.of.get(o)).find(|o| *o != Some(&b)) {
                                return Err(format!("{h} of block {b} shares {a:?}, in {o:?}"));
                            }
                        }
                    }
                }
            }
            names_of.insert(b, ns);
        }
        let held = self
            .at
            .iter()
            .map(|(k, s)| (k.clone(), s.iter().cloned().collect()));
        if !held.eq(at) {
            return Err("the conjuncts of the names by block are not those of the blocks".into());
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
                if (self.up.get(&b) == Some(&n)) == (self.up.get(&n) == Some(&b)) {
                    return Err(format!("block {b} and its name {n} are not linked once"));
                }
                links += 1;
            }
        }
        if self.up.len() != links {
            return Err(format!(
                "parent links {:?}, names of the blocks {names_of:?}, names {:?}",
                self.up, self.name
            ));
        }
        let mut roots: BTreeMap<BlockId, BlockId> = BTreeMap::new();
        for &x in &nodes {
            let mut at = x;
            for _ in 0..=nodes.len() {
                match self.up.get(&at) {
                    Some(&p) => at = p,
                    None => break,
                }
            }
            if self.up.contains_key(&at) {
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
        self.trees.entry(big).or_default().extend(moved);
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
            let next = self.up.get(&cur).copied();
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
    fn path(&self, a: BlockId, b: BlockId) -> (Vec<BlockId>, BlockId) {
        let mut walks = [vec![a], vec![b]];
        let mut seen: [BTreeSet<BlockId>; 2] = [BTreeSet::from([a]), BTreeSet::from([b])];
        let top = if a == b {
            a
        } else {
            'walk: loop {
                let mut stepped = false;
                for side in 0..2 {
                    let last = *walks[side].last().expect("a start");
                    if let Some(&p) = self.up.get(&last) {
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
    /// are moved into it and their names re-hung from it. The merged block's parent is `top`.
    fn merge(&mut self, blocks: &[BlockId], top: Option<BlockId>) -> BlockId {
        let keep = *blocks
            .iter()
            .max_by_key(|&&b| self.members.get(&b).map_or(0, |m| m.len()))
            .expect("a block");
        for &b in blocks.iter().filter(|&&b| b != keep) {
            let moved = self.members.remove(&b).unwrap_or_default();
            for g in &moved {
                let atoms = g.atoms();
                self.put(g, &atoms, Some(keep));
                for a in atoms {
                    if let Atom::Sym(n) = a
                        && let Some(&id) = self.name.get(&n)
                        && self.up.get(&id) == Some(&b)
                    {
                        self.up.insert(id, keep);
                    }
                }
            }
            self.up.remove(&b);
            self.drop_node(b);
            self.members.entry(keep).or_default().extend(moved);
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
            let top = self.up.get(&y).copied();
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
            self.up.get(&top).copied()
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
                .copied();
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
                Atom::Sym(n) => self.syms.add(&n, g),
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
    // `l01_39_reduced_product::disjoint::the_join_of_arms_on_many_disjoint_groups_scales` and
    // `disjoint::the_blocks_of_a_join_are_those_of_the_definition`; COMPLEXITY.md row S29.
    pub fn remove(&mut self, gs: &[Arc<Formula>]) {
        // The conjuncts removed from each block, the blocks in the order `gs` first meets them.
        let mut from: BTreeMap<BlockId, Vec<&Arc<Formula>>> = BTreeMap::new();
        let mut order: Vec<BlockId> = Vec::new();
        for g in gs {
            match self.of.get(g) {
                Some(&b) => {
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
                        let b = self.of[*g];
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
        if ms.is_empty() {
            self.bridge(b, r, (u, iu), (v, iv));
        } else {
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
            if self.up.get(&id) == Some(&b) {
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
        let found = if side == 0 { first } else { second };
        let t = self.fresh();
        let (mut others, mut gaps) = (0isize, 0isize);
        for (x, name) in &found.nodes {
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
        let nodes: OrdSet<BlockId> = found.nodes.iter().map(|(x, _)| *x).collect();
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
    // Complexity tradeoff: placing the block's other conjuncts again (`Blocks::split`) costs
    // O(|b| log n) for each conjunct taken out, so O(d²) to take apart a block of d conjuncts
    // one at a time. The searches cost O((|P| + c + s) log n), where c is the size of the blocks
    // split off, each found by the search that ran out first, so at most twice the smaller side
    // at its cut, and s the cost of the last search, which met its end; a block only taken
    // apart then costs O(d log² n) in all, each conjunct moving to a new block on the smaller
    // side. Still near the block each time: taking a chord out of a long cycle, which leaves
    // one block, when `P` or the meeting search is long, and a name of many conjuncts in other
    // blocks, whose entries the searches pass over. Holm, de Lichtenberg and Thorup's dynamic
    // biconnectivity bounds every case by O(log⁵ n) amortized, at the cost of a far larger
    // structure.
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
            let found = if i == 0 { first } else { second };
            let nb = self.fresh();
            let ms = self.members.get_mut(&b).expect("the block split");
            for h in &found.conjs {
                ms.remove(h);
            }
            for h in &found.conjs {
                self.put(h, &h.atoms(), Some(nb));
            }
            self.members.insert(nb, found.conjs.into_iter().collect());
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
        let parent = self.up.get(&b).copied();
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
                Atom::Sym(n) => self.syms.remove(&n, g),
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
            && self.up.get(&id) == Some(&b)
        {
            self.up.remove(&id);
        }
        self.up.remove(&b);
        self.members.remove(&b);
        self.drop_node(b);
        self.put(g, &g.atoms(), None);
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
        let mut parent: Vec<usize> = (0..index.len()).collect();
        fn root(parent: &mut [usize], mut x: usize) -> usize {
            while parent[x] != x {
                parent[x] = parent[parent[x]];
                x = parent[x];
            }
            x
        }
        let mut used = vec![false; index.len()];
        for (_, ns) in &rest {
            let first = index[&ns[0]];
            for n in ns {
                let i = index[n];
                used[i] = true;
                let (ra, rb) = (root(&mut parent, first), root(&mut parent, i));
                parent[ra] = rb;
            }
        }
        let mut whole = None;
        for (n, &i) in &index {
            let still = self.syms.of(n).next().is_some();
            if !still {
                continue;
            }
            let r = root(&mut parent, i);
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
            if self.up.get(&id) == Some(&b) {
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
            if let Some(&b) = self.of.get(g) {
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

/// The neighbors of a node not yet given: the conjuncts of a name or an atom after the last
/// one given, so that a search can stop after any entry and go on in O(log n), or the atoms of
/// a conjunct.
enum Cursor {
    Name(Arc<str>, Option<Arc<Formula>>),
    Atom(Atom, Option<Arc<Formula>>),
    Atoms(Vec<Node>),
}

/// The first element of `set` after `last`, or its first when `last` is `None`, in O(log n).
fn after<'a>(
    set: &'a OrdSet<Arc<Formula>>,
    last: Option<&Arc<Formula>>,
) -> Option<&'a Arc<Formula>> {
    match last {
        None => set.iter().next(),
        Some(l) => set
            .range::<_, Arc<Formula>>((Bound::Excluded(l), Bound::Unbounded))
            .next(),
    }
}

impl Blocks {
    /// A cursor over the neighbors of `n`.
    fn cursor(&self, n: &Node) -> Cursor {
        match n {
            Node::Name(x, _) => Cursor::Name(x.clone(), None),
            Node::Atom(a) => Cursor::Atom(a.clone(), None),
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
    fn advance(&self, c: &mut Cursor, b: BlockId) -> Option<Option<Node>> {
        let (set, last, check) = match c {
            Cursor::Atoms(ns) => return ns.pop().map(Some),
            Cursor::Name(x, last) => (self.at.get(&(x.clone(), b))?, last, false),
            Cursor::Atom(a, last) => (self.shared.get(a)?, last, true),
        };
        let h = after(set, last.as_ref())?.clone();
        *last = Some(h.clone());
        Some((!check || self.of.get(&h) == Some(&b)).then_some(Node::Conj(h)))
    }
}

/// One side of the search of [`Blocks::route`]: each node reached with the node it was
/// reached from.
struct Search {
    seen: HashMap<Key, (Node, Option<Key>)>,
    queue: VecDeque<Key>,
    cur: Option<(Key, Cursor)>,
}

impl Search {
    fn new(n: Node) -> Search {
        let k = n.key();
        Search {
            seen: HashMap::from([(k.clone(), (n, None))]),
            queue: VecDeque::from([k]),
            cur: None,
        }
    }

    /// Reads one entry: a neighbor in block `b` of the node being read, with that node's key.
    fn step(&mut self, blocks: &Blocks, b: BlockId) -> Option<(Key, Key, Node)> {
        let (k, c) = match &mut self.cur {
            Some(cur) => cur,
            None => {
                let k = self.queue.pop_front()?;
                let c = blocks.cursor(&self.seen[&k].0);
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
struct Flow {
    start: usize,
    end: usize,
    seen: HashSet<Key>,
    queue: VecDeque<(Key, Node)>,
    cur: Option<Cursor>,
    /// The conjuncts reached.
    conjs: Vec<Arc<Formula>>,
    /// The positions of the names between `start` and `end` entered.
    entered: Vec<usize>,
}

impl Flow {
    fn new(path: &[Node], start: usize, end: usize) -> Flow {
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
    fn before<'a>(&self, path: &'a [Node], i: usize) -> Option<&'a Node> {
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
        blocks: &Blocks,
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
                self.cur.insert(blocks.cursor(&n))
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
/// a name with its text, and the one being read with the last conjunct read at it.
struct TreeWalk {
    seen: HashSet<BlockId>,
    nodes: Vec<(BlockId, Option<Arc<str>>)>,
    next: usize,
    cur: Option<(usize, Option<Arc<Formula>>)>,
}

impl TreeWalk {
    fn new((x, id): (&Arc<str>, BlockId)) -> TreeWalk {
        TreeWalk {
            seen: HashSet::from([id]),
            nodes: vec![(id, Some(x.clone()))],
            next: 0,
            cur: None,
        }
    }

    /// Reads one entry: a conjunct of a name, which gives its block, or a conjunct of a block,
    /// which gives its names. Whether anything was left to read.
    fn step(&mut self, blocks: &Blocks) -> bool {
        let (i, last) = match &mut self.cur {
            Some(cur) => cur,
            None => {
                if self.next == self.nodes.len() {
                    return false;
                }
                self.next += 1;
                self.cur.insert((self.next - 1, None))
            }
        };
        let (x, name) = &self.nodes[*i];
        let set = match name {
            Some(n) => blocks.syms.0.get(&**n),
            None => blocks.members.get(x),
        };
        let Some(h) = set.and_then(|s| after(s, last.as_ref())).cloned() else {
            self.cur = None;
            return true;
        };
        *last = Some(h.clone());
        if name.is_some() {
            let b = blocks.of[&h];
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
