//! The linear relation of a scope (step L1.39) as a persistent set of conjuncts, with the
//! conjuncts that mention each name and, of the constraints on each term, the tighter one.
//!
//! A scope is copied for each case of a test and the cases are joined, so the relation is held
//! in persistent maps: a copy costs O(1), a new conjunct O(log n) in the size of the relation,
//! and two relations made from one by a few changes are compared, and their differing
//! conjuncts found, in time near the number of changes. The conjuncts are in the order of
//! formulas, so a relation does not depend on the order its conjuncts were added in.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fmt;
use std::ops::{Bound, RangeBounds};
use std::sync::Arc;

use imbl::{OrdMap, OrdSet};

use super::int::Int;
use super::presburger::{Atom, Con, Factor, Formula, Lin, Model, Rel};

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
}

impl Uses<(usize, Arc<str>)> {
    /// The names kept at `name` with a count in `counts`, in O(log n) and their number.
    fn within(&self, name: &str, counts: impl RangeBounds<usize>) -> Vec<Arc<str>> {
        let Some(s) = self.0.get(name) else {
            return Vec::new();
        };
        // The least name, so that `(c, least)` comes before every entry of count `c`.
        let least: Arc<str> = Arc::from("");
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

/// A conjunction of formulas, `true` when empty.
#[derive(Clone, Debug, Default)]
pub struct Conjuncts {
    /// The conjuncts. `false` is the set of `false` alone.
    set: OrdSet<Arc<Formula>>,
    /// Of the constraints on each term with each relation, the one kept.
    tight: OrdMap<Tight, Arc<Formula>>,
    /// The conjuncts that mention each name, alone or in a product.
    users: Uses<Arc<Formula>>,
    /// The blocks of the conjuncts: the forest of the conjuncts of no star, and each star's
    /// conjuncts as a block of its own outside it ([`Blocks::detach`]).
    blocks: Blocks,
    /// The stars and what keeps them current, apart so that a conjunction is small to move.
    index: Box<StarIndex>,
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
    /// The names of `shapes` of two hubs or more, at each hub.
    multi: Uses<Arc<str>>,
    /// The conjuncts at each name that a name of `shapes` other than it holds.
    owned: Uses<Arc<Formula>>,
    /// The conjuncts at each name of that name alone ([`alone`]).
    solo: Uses<Arc<Formula>>,
    /// The names every conjunct at which is in `owned` or `solo`, as last found.
    clean: OrdSet<Arc<str>>,
    /// The stars ([`Conjuncts::star`]): each leaf's block.
    stars: OrdMap<Arc<str>, BlockId>,
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
    /// Its hubs: the other names its conjuncts mention.
    hubs: Vec<Arc<str>>,
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
    /// The names whose conjuncts or owned conjuncts changed: whether they are clean may have.
    touched: BTreeSet<Arc<str>>,
    /// The conjuncts added, not yet in a block, each with the one it takes the place of.
    placed: Vec<(Arc<Formula>, Option<Arc<Formula>>)>,
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
    /// `a * x + b1 * y1 + … + c >= 0` of names alone with at least one other name, its hubs;
    /// `a` is of one sign at every conjunct, so is each hub's coefficient, each hub is
    /// mentioned by more conjuncts than `x`, and where a conjunct mentions two hubs or more,
    /// `x` is unbounded on the side away from it ([`Conjuncts::bound`]). The leaf's conjuncts
    /// are a star when it has one hub or each of its hubs is clean: every conjunct at the hub
    /// is a leaf's or of the hub alone ([`alone`]), such as a bound on it. A conjunct is the
    /// leaf's of one name at most, since its hubs have more conjuncts than it.
    ///
    /// A star bounds its leaf on one side only, the side its hubs' least or greatest values
    /// bound it from, and a conjunct of two hubs or more holds for a large enough `x`: the
    /// star's projection onto its hubs is a bound on each hub alone, and so is the projection
    /// of the leaves' conjuncts at a clean hub, and its other conjuncts hold of it alone. The
    /// hubs of a star of clean hubs then range over a box, whose corners their products hold,
    /// and a star of one hub lies on no cycle, so in both the star's projection onto `x` is
    /// the projection of the whole relation, and a move of a hub changes `x` alone
    /// and cuts it to a half-line that holds its greatest or least member, which empties
    /// nothing. A star is a block of its own outside the forest ([`Blocks::detach`]).
    pub fn star(&self, x: &str) -> Option<BlockId> {
        self.index.stars.get(x).copied()
    }

    /// The leaf and block of each star ([`Conjuncts::star`]).
    pub fn stars(&self) -> &OrdMap<Arc<str>, BlockId> {
        &self.index.stars
    }

    /// The conjuncts of the stars whose hub is `y`.
    pub fn hanging(&self, y: &str) -> impl Iterator<Item = &Arc<Formula>> {
        self.index.hangs.of(y)
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
            let Formula::Con(c) = &**g else {
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
            let mut others = 0;
            for (a, b) in &c.lin.terms {
                let Atom::Sym(h) = a else {
                    unreachable!("a conjunct of names alone")
                };
                if h == x {
                    continue;
                }
                others += 1;
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
            if others == 0 {
                return Err(why(vec![g.clone()]));
            }
            // `x` is bounded by `g` below when `up`, so a large enough `x` meets it when `x`
            // is unbounded above.
            if others > 1 {
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

    /// Takes `x`'s shape or `Why` out of the indexes; the names whose owned conjuncts change
    /// are touched. Every name to be found again is taken out first ([`Conjuncts::flush`]):
    /// a conjunct whose leaf changes in one flush is then owned by the new leaf alone.
    fn unshape(&mut self, x: &Arc<str>, p: &mut Pending) {
        if let Some(old) = self.index.shapes.remove(x) {
            for g in &old.gs {
                for h in names(g).into_iter().filter(|h| h != x) {
                    self.index.owned.remove(&h, g);
                    p.touched.insert(h);
                }
            }
            for h in &old.hubs {
                self.index.shaped.remove(h, &(old.count, x.clone()));
                if old.hubs.len() > 1 {
                    self.index.multi.remove(h, x);
                }
            }
        }
        if let Some(old) = self.index.whys.remove(x)
            && let Some(h) = &old.count
        {
            self.index.witnessed.remove(h, &(old.size, x.clone()));
        }
    }

    /// Finds `x`'s shape, its old one taken out ([`Conjuncts::unshape`]), and indexes it; the
    /// names whose owned conjuncts change are touched.
    fn reshape(&mut self, x: &Arc<str>, p: &mut Pending) {
        if self.users.count(x) == 0 {
            return;
        }
        match self.shape_of(x) {
            Ok(s) => {
                for g in &s.gs {
                    for h in names(g).into_iter().filter(|h| h != x) {
                        self.index.owned.add(&h, g);
                        p.touched.insert(h);
                    }
                }
                for h in &s.hubs {
                    self.index.shaped.add(h, &(s.count, x.clone()));
                    if s.hubs.len() > 1 {
                        self.index.multi.add(h, x);
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

    /// Notes that `g` came to (`added`) or left each of the names `ns`, whose counts are
    /// already changed: the names whose shape that may change are put in `p`. A name of no
    /// shape stays so as long as what its `Why` names stands, which costs O(log n) here: so a
    /// hub of many conjuncts is not looked at again for each conjunct that comes.
    fn counted(&mut self, g: &Arc<Formula>, ns: &BTreeSet<Arc<str>>, added: bool, p: &mut Pending) {
        for n in ns {
            p.touched.insert(n.clone());
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
    /// whose hub became clean or not; then places each conjunct added and not yet in a block,
    /// in the forest in place of the one it replaces when it can.
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
        for h in &p.touched {
            let (all, held) = (self.users.count(h), self.index.owned.count(h));
            let now = all > 0 && all == held + self.index.solo.count(h);
            if now != self.index.clean.contains(h) {
                if now {
                    self.index.clean.insert(h.clone());
                } else {
                    self.index.clean.remove(h);
                }
                check.extend(self.index.multi.of(h).cloned());
            }
        }
        // The stars that go or change first, so that a conjunct moving from one leaf's star to
        // another's is out of its block when the second takes it.
        let mut loose: Vec<Arc<Formula>> = Vec::new();
        let mut new: Vec<(Arc<str>, Arc<Shape>)> = Vec::new();
        for x in &check {
            let shape = self.index.shapes.get(x).filter(|s| {
                s.hubs.len() == 1 || s.hubs.iter().all(|h| self.index.clean.contains(h))
            });
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
            Formula::And(Arc::new(gs))
        }
    }

    /// Each constraint, conjunct by conjunct.
    pub fn cons(&self) -> Vec<&Con> {
        self.set.iter().flat_map(|g| g.cons()).collect()
    }

    /// The conjunction with `f`: a conjunction's parts are added each, `true` is dropped and
    /// `false` absorbs, and of two constraints on one term with one relation the tighter
    /// alone is kept, as [`Formula::and`] does. A conjunct of no atoms, such as the `!(0 == 0)`
    /// of a test `x != x`, is decided at once: it is `true` or `false`, since no block holds
    /// it and no projection would read it.
    pub fn and(&mut self, f: Formula) {
        let mut p = Pending::default();
        self.and_held(f, &mut Held::new(), &mut p);
        self.flush(p);
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
        let mut seen: HashSet<*const Vec<Formula>> = HashSet::new();
        // The shared conjunctions read, held so that their addresses are not reused.
        let mut read: Vec<Formula> = Vec::new();
        let mut stack = vec![f];
        while let Some(g) = stack.pop() {
            let Formula::And(gs) = &g else {
                self.and_one(g, held, p);
                continue;
            };
            if Arc::strong_count(gs) == 1 {
                stack.extend(g.into_parts().expect("a conjunction").into_iter().rev());
            } else if seen.insert(Arc::as_ptr(gs)) {
                stack.extend(gs.iter().rev().cloned());
                read.push(g);
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
        let mut p = Pending::default();
        for g in gs {
            self.and_held(g.forget(name), &mut Held::new(), &mut p);
        }
        self.flush(p);
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
/// forest, each tree rooted somewhere and held by parent links, with a union-find of the trees.
///
/// A new conjunct is a block of its own: it is linked to each tree of a name it mentions that
/// is not yet its own, by rerooting the smaller tree (so a node is rerooted O(log n) times),
/// and when it meets its own tree a second time, the blocks on the tree path between are
/// merged into one, the smaller blocks' conjuncts moved into the largest (so a conjunct is
/// moved O(log n) times): with the persistent maps, O(log² n) amortized per conjunct. A
/// removed conjunct that is a block alone and shares at most one name with the rest is
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
    /// The union-find of the trees: each node's link toward its tree's representative.
    link: OrdMap<BlockId, BlockId>,
    /// The number of nodes of each tree, at its representative.
    size: OrdMap<BlockId, usize>,
    /// The conjuncts that mention each name as an atom of its own.
    syms: Uses<Arc<Formula>>,
    /// The conjuncts that mention each atom that is not a name.
    shared: OrdMap<Atom, OrdSet<Arc<Formula>>>,
    /// The blocks apart from the forest, each its own tree ([`Blocks::detach`]).
    apart: OrdSet<BlockId>,
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

    /// A new block of the conjuncts `gs`, none in a block, apart from the forest: no name or
    /// tree links it, so it is its own tree. In O(log n) per conjunct.
    pub fn detach(&mut self, gs: impl IntoIterator<Item = Arc<Formula>>) -> BlockId {
        let b = self.fresh();
        let mut ms = OrdSet::new();
        for g in gs {
            let was = self.of.insert(g.clone(), b);
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
            self.of.remove(&g);
        }
    }

    fn fresh(&mut self) -> BlockId {
        self.next += 1;
        self.next
    }

    /// The representative of `x`'s tree. The union-find links smaller trees under larger and
    /// never compresses, so that it stays persistent: O(log n) links.
    fn find(&self, mut x: BlockId) -> BlockId {
        while let Some(&p) = self.link.get(&x) {
            x = p;
        }
        x
    }

    fn tree_size(&self, r: BlockId) -> usize {
        self.size.get(&r).copied().unwrap_or(1)
    }

    fn union(&mut self, a: BlockId, b: BlockId) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return;
        }
        let (sa, sb) = (self.tree_size(ra), self.tree_size(rb));
        let (small, big) = if sa < sb { (ra, rb) } else { (rb, ra) };
        self.link.insert(small, big);
        self.size.remove(&small);
        self.size.insert(big, sa + sb);
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
                self.of.insert(g.clone(), keep);
                for a in g.atoms() {
                    if let Atom::Sym(n) = a
                        && let Some(&id) = self.name.get(&n)
                        && self.up.get(&id) == Some(&b)
                    {
                        self.up.insert(id, keep);
                    }
                }
            }
            self.up.remove(&b);
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
            let keep = self.merge(&[x, y], top);
            self.union(a, b);
            return keep;
        }
        let (path, top) = self.path(a, b);
        let blocks: Vec<BlockId> = path
            .iter()
            .copied()
            .filter(|n| self.members.contains_key(n))
            .collect();
        if blocks.len() < 2 {
            return a;
        }
        let parent = if self.members.contains_key(&top) {
            self.up.get(&top).copied()
        } else {
            Some(top)
        };
        let keep = self.merge(&blocks, parent);
        for &n in &path {
            if n != top && !self.members.contains_key(&n) {
                self.up.insert(n, keep);
            }
        }
        keep
    }

    /// Places `g`, already indexed by its atoms, in the forest.
    fn place(&mut self, g: &Arc<Formula>) {
        let b = self.fresh();
        self.members.insert(b, OrdSet::unit(g.clone()));
        self.of.insert(g.clone(), b);
        let atoms = g.atoms();
        let mut met: Vec<BlockId> = Vec::new();
        for a in &atoms {
            if let Atom::Sym(n) = a {
                match self.name.get(n) {
                    Some(&id) => met.push(id),
                    None => {
                        let id = self.fresh();
                        self.name.insert(n.clone(), id);
                        self.up.insert(id, b);
                        self.union(id, b);
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
        let Some(b) = self.of.remove(old) else {
            return self.add(new);
        };
        self.of.insert(new.clone(), b);
        if let Some(m) = self.members.get_mut(&b) {
            m.remove(old);
            m.insert(new.clone());
        }
        for a in old.atoms() {
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

    /// Removes the conjuncts `gs`, block by block. A block that loses its one conjunct, which
    /// shares at most one name and no other atom with the rest, is unlinked; a block that loses
    /// some of its conjuncts is split once by placing its other conjuncts again
    /// (`Blocks::split`); if that fails, the blocks of every conjunct linked to one of `gs`
    /// are built again. Each block is split once for all the conjuncts it loses, so a removal
    /// costs near the blocks it touches, not their size times the conjuncts removed.
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
        for a in &atoms {
            if let Atom::Sym(n) = a
                && kept.first() != Some(&n)
                && let Some(id) = self.name.remove(n)
            {
                self.up.remove(&id);
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
        self.of.remove(g);
        true
    }

    /// Removes `out`, conjuncts of block `b` already out of `syms`, from it by placing the
    /// block's other conjuncts again, in time near the block's size, when that keeps the tree
    /// whole: every atom of the block is a name, and the other conjuncts link every name of
    /// the block that some conjunct still mentions. Removing `b` from the tree leaves one piece
    /// per name of it, all in one tree of the union-find, which cannot split; the pieces of
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
        for (h, _) in &rest {
            self.of.remove(h);
        }
        for g in out {
            self.of.remove(*g);
        }
        // The local pieces: each kept name of the block and each new block, with the piece
        // that holds `top`, which hangs from the rest of the tree, never rerooted.
        let mut piece: BTreeMap<BlockId, BlockId> = BTreeMap::new();
        let mut count: BTreeMap<BlockId, usize> = BTreeMap::new();
        let mut removed = 1usize;
        for n in index.keys() {
            let Some(&id) = self.name.get(n) else {
                continue;
            };
            if self.syms.of(n).next().is_none() {
                self.name.remove(n);
                self.up.remove(&id);
                removed += 1;
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
        let any = *self.name.get(&rest[0].1[0]).expect("a kept name");
        for (h, ns) in &rest {
            let nb = self.fresh();
            self.members.insert(nb, OrdSet::unit(h.clone()));
            self.of.insert(h.clone(), nb);
            self.union(nb, any);
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
        let r = self.find(any);
        let s = self.tree_size(r) + rest.len();
        self.size.insert(r, s.saturating_sub(removed).max(1));
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
        for g in gs.iter().chain(&found) {
            if let Some(b) = self.of.remove(g) {
                self.members.remove(&b);
                self.up.remove(&b);
            }
            for a in g.atoms() {
                if let Atom::Sym(n) = a
                    && let Some(id) = self.name.remove(&n)
                {
                    self.up.remove(&id);
                }
            }
        }
        for g in &found {
            self.place(g);
        }
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
