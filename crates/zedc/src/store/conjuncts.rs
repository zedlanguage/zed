//! The linear relation of a scope (step L1.39) as a persistent set of conjuncts, with the
//! conjuncts that mention each name and, of the constraints on each term, the tighter one.
//!
//! A scope is copied for each case of a test and the cases are joined, so the relation is held
//! in persistent maps: a copy costs O(1), a new conjunct O(log n) in the size of the relation,
//! and two relations made from one by a few changes are compared, and their differing
//! conjuncts found, in time near the number of changes. The conjuncts are in the order of
//! formulas, so a relation does not depend on the order its conjuncts were added in.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use imbl::{OrdMap, OrdSet};

use super::int::Int;
use super::presburger::{Atom, Con, Formula, Rel};

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

    /// The names that are used.
    pub fn names(&self) -> impl Iterator<Item = &Arc<str>> {
        self.0.keys()
    }
}

/// The key of a constraint for the rule that keeps the tighter of two: its term and relation.
type Tight = (BTreeMap<Atom, Int>, Rel);

/// A conjunction of formulas, `true` when empty.
#[derive(Clone, Debug, Default)]
pub struct Conjuncts {
    /// The conjuncts. `false` is the set of `false` alone.
    set: OrdSet<Arc<Formula>>,
    /// Of the constraints on each term with each relation, the one kept.
    tight: OrdMap<Tight, Arc<Formula>>,
    /// The conjuncts that mention each name, alone or in a product.
    users: Uses<Arc<Formula>>,
    /// The blocks of the conjuncts.
    blocks: Blocks,
}

impl PartialEq for Conjuncts {
    fn eq(&self, other: &Conjuncts) -> bool {
        self.set == other.set
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
                out.insert(x);
                out.insert(y);
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

    /// The conjunction as one formula, as [`Formula::and`] gives it.
    pub fn formula(&self) -> Formula {
        let mut gs: Vec<Formula> = self.set.iter().map(|g| (**g).clone()).collect();
        if gs.len() == 1 {
            gs.pop().expect("one")
        } else {
            Formula::And(gs)
        }
    }

    /// Each constraint, conjunct by conjunct.
    pub fn cons(&self) -> Vec<&Con> {
        self.set.iter().flat_map(|g| g.cons()).collect()
    }

    /// The conjunction with `f`: a conjunction's parts are added each, `true` is dropped and
    /// `false` absorbs, and of two constraints on one term with one relation the tighter
    /// alone is kept, as [`Formula::and`] does.
    pub fn and(&mut self, f: Formula) {
        match f {
            Formula::And(gs) => gs.into_iter().for_each(|g| self.and_one(g)),
            g => self.and_one(g),
        }
    }

    fn and_one(&mut self, g: Formula) {
        if self.set.iter().next().is_some_and(|f| is_false(f)) {
            return;
        }
        match &g {
            Formula::Or(gs) if gs.is_empty() => {
                *self = Conjuncts::default();
                self.set.insert(Arc::new(g));
                return;
            }
            Formula::And(_) => return self.and(g),
            _ => {}
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
                self.unindex(&old);
                looser = Some(old);
            } else if c.rel == Rel::Eq && c.lin.constant != o.lin.constant {
                self.and_one(Formula::bottom());
                return;
            } else {
                return;
            }
        }
        let g = Arc::new(g);
        if self.set.contains(&g) {
            return;
        }
        for n in names(&g) {
            self.users.add(&n, &g);
        }
        if let Formula::Con(c) = &*g {
            self.tight.insert((c.lin.terms.clone(), c.rel), g.clone());
        }
        match looser {
            Some(old) => self.blocks.replace(&old, &g),
            None => self.blocks.add(&g),
        }
        self.set.insert(g);
    }

    /// Removes `g` from the set and from every index but the blocks; whether it was there.
    fn unindex(&mut self, g: &Arc<Formula>) -> bool {
        if self.set.remove(g).is_none() {
            return false;
        }
        for n in names(g) {
            self.users.remove(&n, g);
        }
        if let Formula::Con(c) = &**g {
            let key = (c.lin.terms.clone(), c.rel);
            if self.tight.get(&key) == Some(g) {
                self.tight.remove(&key);
            }
        }
        true
    }

    /// Removes the conjunct `g`.
    pub fn remove(&mut self, g: &Arc<Formula>) {
        if self.unindex(g) {
            self.blocks.remove(std::slice::from_ref(g));
        }
    }

    /// The conjunction with every conjunct that mentions `name` replaced by
    /// [`Formula::forget`] of it, which says nothing of `name`: in time near the conjuncts
    /// that mention it, but for the blocks, which are built again over the conjuncts linked
    /// to them when one is not a leaf of its tree ([`Blocks::remove`]).
    pub fn forget(&mut self, name: &Arc<str>) {
        let gs: Vec<Arc<Formula>> = self.mentioning(name).cloned().collect();
        for g in &gs {
            self.unindex(g);
        }
        self.blocks.remove(&gs);
        for g in gs {
            self.and(g.forget(name));
        }
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
/// unlinked in O(log n); any other removal rebuilds the blocks of the conjuncts linked to it,
/// in time near their number. The blocks do not depend on the order the conjuncts came in;
/// the roots and the numbers do, and nothing reads them but this forest.
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
    /// and its block merged with the other's.
    fn unite(&mut self, a: BlockId, b: BlockId) {
        if self.find(a) != self.find(b) {
            // Two blocks of different trees, which share an atom other than a name.
            let small_first = self.tree_size(self.find(a)) <= self.tree_size(self.find(b));
            let (x, y) = if small_first { (a, b) } else { (b, a) };
            self.reroot(x);
            let top = self.up.get(&y).copied();
            self.merge(&[x, y], top);
            self.union(a, b);
            return;
        }
        let (path, top) = self.path(a, b);
        let blocks: Vec<BlockId> = path
            .iter()
            .copied()
            .filter(|n| self.members.contains_key(n))
            .collect();
        if blocks.len() < 2 {
            return;
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
        for id in met {
            let cur = self.of[g];
            if self.find(cur) == self.find(id) {
                self.unite(cur, id);
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
            if let Some(o) = other {
                let cur = self.of[g];
                if o != cur {
                    self.unite(cur, o);
                }
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

    /// Removes the conjuncts `gs`. One that is a block alone and shares at most one name and
    /// no other atom with the rest is unlinked; if any other is removed, the blocks of every
    /// conjunct linked to one of `gs` are built again.
    pub fn remove(&mut self, gs: &[Arc<Formula>]) {
        let mut rebuild = false;
        for g in gs {
            let atoms = g.atoms();
            for a in &atoms {
                match a {
                    Atom::Sym(n) => self.syms.remove(n, g),
                    a => {
                        if let Some(s) = self.shared.get_mut(a) {
                            s.remove(g);
                            if s.is_empty() {
                                self.shared.remove(a);
                            }
                        }
                    }
                }
            }
            if rebuild {
                continue;
            }
            let Some(b) = self.of.get(g).copied() else {
                continue;
            };
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
                rebuild = true;
                continue;
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
        }
        if rebuild {
            self.rebuild(gs);
        }
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
