//! Provenance (step L1.20, DESIGN.md sec:keypaths): the fact address of every value a run
//! computes, and the facts each one read.
//!
//! A fact is one node instance: a node of the term together with the instances of the
//! regions around it (sec:kernel, the objects of the dependency theorem). Its address is the pair of a
//! static [`NodeAddress`], code identity, and a dynamic keypath, data identity, and no two
//! facts of a run share one. A run records its facts when
//! [`Evaluator::with_provenance`](crate::Evaluator::with_provenance) asks for them; the
//! record is the run graph, each fact naming the facts it read.

use imbl::OrdMap;
/// The persistent vector of a fact address's node and keypath.
pub use imbl::Vector;
use imbl::ordmap::DiffItem;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use crate::family::{Family, Id};
use crate::term::{FixKind, Shared, Term};
use crate::value::{Items, Value};

/// The position of a node in a term: the child index taken at each node on the way down from
/// the root, in the order of [`child`]; the root's position is empty. A position is read from
/// the term's structure alone: a subterm that two places of a term share, as a term built by
/// cloning does, has a position at each, and no position depends on where the term sits in
/// memory or on the order a run reaches its nodes. Positions are ordered as the nodes are in
/// the term's preorder. A position shares the path above it with its parent's.
#[derive(Clone, Default)]
pub struct Position(Option<Arc<Link>>);

/// The last step of a position below the root.
struct Link {
    up: Position,
    child: u32,
    depth: u32,
    hash: u64,
}

impl Position {
    /// The root's position.
    pub fn root() -> Self {
        Position(None)
    }

    /// The position of child `i` of the node at `self`.
    pub fn child(&self, i: u32) -> Self {
        let hash = (self.hash_value().rotate_left(26) ^ (u64::from(i) + 1))
            .wrapping_mul(0x9E37_79B9_7F4A_7C15);
        let hash = crate::address::short64(hash);
        Position(Some(Arc::new(Link {
            up: self.clone(),
            child: i,
            depth: self.depth() + 1,
            hash,
        })))
    }

    /// The number of steps from the root.
    pub fn depth(&self) -> u32 {
        self.0.as_ref().map_or(0, |l| l.depth)
    }

    /// The child indices from the root down.
    pub fn path(&self) -> Vec<u32> {
        let mut out = Vec::with_capacity(self.depth() as usize);
        let mut at = self;
        while let Some(l) = &at.0 {
            out.push(l.child);
            at = &l.up;
        }
        out.reverse();
        out
    }

    fn hash_value(&self) -> u64 {
        self.0.as_ref().map_or(0, |l| l.hash)
    }

    fn up(&self) -> &Position {
        self.0.as_ref().map_or(self, |l| &l.up)
    }
}

impl Drop for Position {
    /// Frees a long path one link at a time, not by recursion.
    fn drop(&mut self) {
        let mut next = self.0.take();
        while let Some(link) = next {
            next = Arc::into_inner(link).and_then(|mut l| l.up.0.take());
        }
    }
}

impl PartialEq for Position {
    /// Compares index by index from the bottom; a link both positions share ends the walk.
    fn eq(&self, other: &Self) -> bool {
        if self.depth() != other.depth() || self.hash_value() != other.hash_value() {
            return false;
        }
        let (mut a, mut b) = (self, other);
        while let (Some(x), Some(y)) = (&a.0, &b.0) {
            if Arc::ptr_eq(x, y) {
                return true;
            }
            if x.child != y.child {
                return false;
            }
            (a, b) = (&x.up, &y.up);
        }
        true
    }
}

impl Eq for Position {}

impl Ord for Position {
    /// The order of the paths, index by index from the root, a path before the paths below it.
    /// It walks up to the common ancestor, so it costs the distance to it: `O(depth)` for two
    /// positions far apart in a deep term. Many positions are kept by hash, not by this order.
    fn cmp(&self, other: &Self) -> Ordering {
        let (mut a, mut b) = (self, other);
        while a.depth() > b.depth() {
            a = a.up();
        }
        while b.depth() > a.depth() {
            b = b.up();
        }
        // The walk goes up, so the last difference it meets is the one nearest the root.
        let mut first = Ordering::Equal;
        while let (Some(x), Some(y)) = (&a.0, &b.0) {
            if Arc::ptr_eq(x, y) {
                break;
            }
            if x.child != y.child {
                first = x.child.cmp(&y.child);
            }
            (a, b) = (&x.up, &y.up);
        }
        first.then(self.depth().cmp(&other.depth()))
    }
}

impl PartialOrd for Position {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Hash for Position {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash_value());
    }
}

impl fmt::Display for Position {
    /// Each child index after a dot: `.` is the root, `.1.0` the first child of its second.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let path = self.path();
        if path.is_empty() {
            return f.write_str(".");
        }
        path.iter().try_for_each(|i| write!(f, ".{i}"))
    }
}

impl fmt::Debug for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// The static half of a fact address: the position of each call site through which the run
/// entered the function holding the node, and then the node's own position. Only equality and
/// order mean anything; the positions change with the build (sec:keypaths, the opaque token).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct NodeAddress(pub Vector<Position>);

impl NodeAddress {
    /// The node's own position, the last.
    pub fn position(&self) -> &Position {
        self.0.last().expect("a node address names a node")
    }
}

/// A fact address: (static node address, dynamic keypath). The keypath holds the wave stamp,
/// then each enclosing region's coordinate: a family key, a generation number, an iterate
/// of a lattice `fix`, the key of a definedness `fix` entry, the step of a `fold`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct FactAddress {
    /// The code identity.
    pub node: NodeAddress,
    /// The data identity.
    pub keypath: Vector<Value>,
}

impl fmt::Display for FactAddress {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let node: Vec<String> = self.node.0.iter().map(Position::to_string).collect();
        let keys: Vec<String> = self.keypath.iter().map(Value::to_string).collect();
        write!(f, "{}@({})", node.join("/"), keys.join(", "))
    }
}

/// One node instance of a run.
#[derive(Clone, Debug)]
pub struct Fact {
    /// Where it is.
    pub address: FactAddress,
    /// Its value; `None` for a function.
    pub value: Option<Value>,
    /// The facts it read, by index into [`Provenance::facts`], in the order it read them.
    pub inputs: Vec<usize>,
}

/// The run graph of one evaluation: its facts, each after the facts it read.
#[derive(Clone, Debug)]
pub struct Provenance {
    pub(crate) term: Term,
    pub(crate) facts: Vec<Fact>,
}

impl Provenance {
    /// Every fact, in the order the run completed them.
    pub fn facts(&self) -> &[Fact] {
        &self.facts
    }

    /// The fact the run's result came from, the last one completed.
    pub fn result(&self) -> usize {
        self.facts.len() - 1
    }

    /// The term at `node`'s position, found by walking down to it: `O(depth)`. The terms of
    /// many facts are read from [`Provenance::fact_terms`].
    pub fn term(&self, node: &NodeAddress) -> &Term {
        let at = node.position();
        at.path().into_iter().fold(&self.term, |t, i| {
            child(t, i).unwrap_or_else(|| panic!("no node at position {at}"))
        })
    }

    /// The term of each fact, by the fact's index: each position is found from its parent's
    /// once, so the work is the number of distinct positions, not the sum of their depths.
    pub fn fact_terms(&self) -> Vec<&Term> {
        let mut known = HashMap::new();
        self.facts
            .iter()
            .map(|f| self.resolve(f.address.node.position(), &mut known))
            .collect()
    }

    fn resolve<'a>(
        &'a self,
        p: &'a Position,
        known: &mut HashMap<&'a Position, &'a Term>,
    ) -> &'a Term {
        // The positions from `p` up to the first one known, nearest first.
        let mut todo = Vec::new();
        let mut at = p;
        let mut t = loop {
            if let Some(t) = known.get(at) {
                break *t;
            }
            match &at.0 {
                Some(l) => {
                    todo.push((at, l.child));
                    at = &l.up;
                }
                None => break &self.term,
            }
        };
        while let Some((q, i)) = todo.pop() {
            t = child(t, i).unwrap_or_else(|| panic!("no node at position {q}"));
            known.insert(q, t);
        }
        t
    }

    /// The addresses held by more than one fact, in fact order; a correct run has none
    /// (sec:keypaths, one writer per fact address). Node addresses are found by their cached
    /// hashes, not by [`Position`]'s order, whose comparison walks up to the common ancestor;
    /// the keypaths of one node are ordered, since a [`Value`] has no hash.
    pub fn repeated(&self) -> Vec<&FactAddress> {
        let mut seen: HashMap<&NodeAddress, BTreeSet<&Vector<Value>>> = HashMap::new();
        let mut out = Vec::new();
        for f in &self.facts {
            let a = &f.address;
            if !seen.entry(&a.node).or_default().insert(&a.keypath) {
                out.push(&f.address);
            }
        }
        out
    }

    /// The origins of the failure that fact `i` holds: for each distinct failure, the facts
    /// where it first appeared, so a merged `#errs` keeps the origins of all its operands
    /// rather than a winner (sec:failure). A failure first appears at a fact none of whose
    /// inputs holds it. Empty when the fact holds no failure.
    pub fn origins(&self, i: usize) -> BTreeSet<usize> {
        let Some(v @ Value::Atom(_)) = &self.facts[i].value else {
            return BTreeSet::new();
        };
        let members: BTreeSet<&Value> = match v.errs() {
            Some(set) => set.keys().collect(),
            None => BTreeSet::from([v]),
        };
        let mut held = Held {
            members: &members,
            sets: HashMap::new(),
            seen: HashSet::new(),
            done: HashMap::new(),
            made: HashMap::new(),
        };
        // One backward pass over the facts, newest first: a fact's inputs completed before it,
        // so every fact that reaches `j` is taken before `j`. `traced[j]` holds the members
        // whose search reaches fact `j`; the search of member `m` goes on to each input that
        // holds `m`, and `j` is an origin of `m` when no input holds it. The sets are
        // persistent maps, and a set found from another shares its nodes, so the common
        // members of two sets are read from their difference when it is short: along a chain
        // of products, each holding one member more than the last, a step costs `O(log n)`.
        let mut traced: BTreeMap<usize, Found> = BTreeMap::from([(i, held.of(v))]);
        let mut out = BTreeSet::new();
        while let Some((j, at_j)) = traced.pop_last() {
            let mut found = Found::new();
            for &k in &self.facts[j].inputs {
                debug_assert!(k < j, "a fact reads only facts completed before it");
                let Some(v) = &self.facts[k].value else {
                    continue;
                };
                let common = meet(&at_j, &held.of(v));
                if !common.is_empty() {
                    found = join(&found, &common);
                    let t = traced.entry(k).or_default();
                    *t = join(t, &common);
                }
            }
            if found.len() < at_j.len() {
                out.insert(j);
            }
        }
        out
    }
}

/// A set of failures. In the set of a family each failure maps to the number of the family's
/// entries that hold it, so that a family's set can be found from another family's by the
/// difference of the two; in other sets the number means nothing.
type Found<'a> = OrdMap<&'a Value, u32>;

/// A non-empty sequence or a family, each named by its id ([`Items::id`], [`Family::id`]). An
/// id is only tested for equality, as a key of `sets` and `seen`, which are never iterated: no
/// order and nothing in the result depends on its value, and the origins come out in fact
/// order. The empty sequence is never entered or looked up.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Part {
    Items(Id),
    Family(Id),
}

/// A family whose set is found from the set of `base` and the difference of the two maps.
type FromBase<'a> = (&'a Family, Vec<DiffItem<'a, 'a, Value, Value>>);

/// What [`Held::of`] does next.
enum Task<'a> {
    Enter(&'a Value),
    /// The set of the sequence, its values' sets found.
    Items(&'a Items),
    /// The set of the family, the sets it needs found.
    Family(&'a Family, Option<FromBase<'a>>),
}

/// The failures of `members` that values hold: that a value is, has as a member of an
/// `#errs`, or holds in a tuple, a family or a payload. A value shares its tuples and families
/// with other values, so the set of each is found once, keyed by its id, and a walk
/// over a value is `O(distinct parts)`, not `O(paths)`.
struct Held<'m, 'a> {
    members: &'m BTreeSet<&'a Value>,
    sets: HashMap<Part, Found<'a>>,
    /// The parts entered: a part is entered once, and its set is found before any part that
    /// holds it, since a value holds no part that holds it.
    seen: HashSet<Part>,
    /// The families whose sets are found, by id.
    done: HashMap<Id, &'a Family>,
    /// The families whose sets are found, by the id of the family each was made from.
    made: HashMap<Id, &'a Family>,
}

impl<'a> Held<'_, 'a> {
    fn of(&mut self, v: &'a Value) -> Found<'a> {
        let mut todo = vec![Task::Enter(v)];
        while let Some(task) = todo.pop() {
            match task {
                Task::Enter(v) => self.enter(v, &mut todo),
                Task::Items(xs) => {
                    let s = xs.iter().fold(Found::new(), |s, x| join(&s, &self.read(x)));
                    self.sets.insert(Part::Items(xs.id()), s);
                }
                Task::Family(f, base) => {
                    let s = self.family(f, base);
                    self.sets.insert(Part::Family(f.id()), s);
                    self.done.insert(f.id(), f);
                    if f.from() != 0 {
                        self.made.entry(f.from()).or_insert(f);
                    }
                }
            }
        }
        self.read(v)
    }

    /// Plans the sets of the parts of `v` not yet entered.
    fn enter(&mut self, v: &'a Value, todo: &mut Vec<Task<'a>>) {
        match v {
            Value::Atom(a) => self.enter_items(&a.args, todo),
            Value::Tuple(xs) | Value::Path(xs) => self.enter_items(xs, todo),
            Value::Family(f) if !f.is_empty() && self.seen.insert(Part::Family(f.id())) => {
                let base = self.base(f);
                let needs: Vec<&'a Value> = match &base {
                    None => f.0.values().collect(),
                    Some((_, diff)) => diff
                        .iter()
                        .flat_map(|d| match d {
                            DiffItem::Add(_, e) | DiffItem::Remove(_, e) => [Some(*e), None],
                            DiffItem::Update { old, new } => [Some(old.1), Some(new.1)],
                        })
                        .flatten()
                        .collect(),
                };
                todo.push(Task::Family(f, base));
                todo.extend(needs.into_iter().map(Task::Enter));
            }
            _ => {}
        }
    }

    fn enter_items(&mut self, xs: &'a Items, todo: &mut Vec<Task<'a>>) {
        if !xs.is_empty() && self.seen.insert(Part::Items(xs.id())) {
            todo.push(Task::Items(xs));
            todo.extend(xs.iter().map(Task::Enter));
        }
    }

    /// The family `f`'s set is found from the set of the family it was made from, or of one
    /// made from it, when that set is found and their difference lists fewer items than `f` has
    /// entries; otherwise from each entry. The two share all but the nodes the change copied,
    /// which the difference skips, and it is abandoned as soon as it is as long as `f`, so
    /// either way the work is `O(|f|)` items. Only such a pair is compared: the difference of
    /// two families that share no nodes compares the values at each common key whole, which for
    /// nested families is as deep as they are.
    fn base(&self, f: &'a Family) -> Option<FromBase<'a>> {
        let base = match self.done.get(&f.from()) {
            Some(base) if f.from() != 0 => *base,
            _ => *self.made.get(&f.id())?,
        };
        let mut diff = Vec::new();
        for d in base.0.diff(&f.0) {
            if diff.len() >= f.len() {
                return None;
            }
            diff.push(d);
        }
        Some((base, diff))
    }

    fn family(&self, f: &'a Family, base: Option<FromBase<'a>>) -> Found<'a> {
        let Some((base, diff)) = base else {
            let mut s = Found::new();
            for e in f.0.values() {
                self.read(e).keys().for_each(|x| count(&mut s, x, true));
            }
            return s;
        };
        let mut s = self.sets[&Part::Family(base.id())].clone();
        for d in diff {
            match d {
                DiffItem::Add(_, e) => self.read(e).keys().for_each(|x| count(&mut s, x, true)),
                DiffItem::Remove(_, e) => self.read(e).keys().for_each(|x| count(&mut s, x, false)),
                DiffItem::Update { old, new } => {
                    let (old, new) = (self.read(old.1), self.read(new.1));
                    for d in old.diff(&new) {
                        match d {
                            DiffItem::Add(x, _) => count(&mut s, x, true),
                            DiffItem::Remove(x, _) => count(&mut s, x, false),
                            DiffItem::Update { .. } => {}
                        }
                    }
                }
            }
        }
        s
    }

    /// The set of `v`, the sets of its parts found.
    fn read(&self, v: &'a Value) -> Found<'a> {
        let items = |xs: &Items| match xs.is_empty() {
            true => Found::new(),
            false => self.sets[&Part::Items(xs.id())].clone(),
        };
        let mut s = match v {
            Value::Atom(a) => items(&a.args),
            Value::Tuple(xs) | Value::Path(xs) => items(xs),
            Value::Family(f) if !f.is_empty() => self.sets[&Part::Family(f.id())].clone(),
            _ => Found::new(),
        };
        if let Some(&m) = self.members.get(v)
            && !s.contains_key(m)
        {
            s.insert(m, 1);
        }
        s
    }
}

/// Counts one more entry holding `x`, or one fewer.
fn count<'a>(s: &mut Found<'a>, x: &&'a Value, more: bool) {
    let n = s.get(x).copied().unwrap_or(0);
    match (more, n) {
        (true, _) => {
            s.insert(*x, n + 1);
        }
        (false, 1) => {
            s.remove(x);
        }
        (false, _) => {
            debug_assert!(n > 1, "a failure an entry held is counted");
            s.insert(*x, n - 1);
        }
    }
}

/// The difference from `from` to `to`, when it lists fewer items than the smaller set has.
fn short_diff<'s, 'a>(
    from: &'s Found<'a>,
    to: &'s Found<'a>,
) -> Option<Vec<DiffItem<'s, 's, &'a Value, u32>>> {
    let limit = from.len().min(to.len());
    let mut diff = Vec::new();
    for d in from.diff(to) {
        if diff.len() >= limit {
            return None;
        }
        diff.push(d);
    }
    Some(diff)
}

/// The failures in both `a` and `b`: the smaller set less what the difference lists as only
/// in it, when the difference is short, and otherwise each member of the smaller set looked
/// up in the larger. The work is `O(min(|a|, |b|) log n)`.
fn meet<'a>(a: &Found<'a>, b: &Found<'a>) -> Found<'a> {
    let (small, large) = if a.len() <= b.len() { (a, b) } else { (b, a) };
    match short_diff(small, large) {
        Some(diff) => {
            let mut out = small.clone();
            for d in diff {
                if let DiffItem::Remove(x, _) = d {
                    out.remove(x);
                }
            }
            out
        }
        None => small
            .iter()
            .filter(|(x, _)| large.contains_key(*x))
            .map(|(x, n)| (*x, *n))
            .collect(),
    }
}

/// The failures in `a` or `b`: the larger set with what is only in the smaller added, read from
/// the difference when it is short. The work is `O(min(|a|, |b|) log n)`.
fn join<'a>(a: &Found<'a>, b: &Found<'a>) -> Found<'a> {
    let (small, large) = if a.len() <= b.len() { (a, b) } else { (b, a) };
    let mut out = large.clone();
    match short_diff(large, small) {
        Some(diff) => {
            for d in diff {
                if let DiffItem::Add(x, n) = d {
                    out.insert(*x, *n);
                }
            }
        }
        None => {
            for (x, n) in small.iter() {
                if !out.contains_key(x) {
                    out.insert(*x, *n);
                }
            }
        }
    }
    out
}

/// Child `i` of `t`, in the order that numbers the positions.
pub fn child<'a>(t: &'a Term, i: u32) -> Option<&'a Term> {
    let i = i as usize;
    fn pick<'a>(ts: &[&'a Shared], i: usize) -> Option<&'a Term> {
        ts.get(i).map(|&t| &**t)
    }
    let nth = |ts: &[&'a Shared]| pick(ts, i);
    match t {
        Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => None,
        Term::Lam(_, body) => nth(&[body]),
        Term::App(f, args) => match i {
            0 => Some(&**f),
            _ => args.get(i - 1),
        },
        Term::Prim(_, args) => args.get(i),
        Term::Let(_, e, body) => nth(&[e, body]),
        Term::If(c, a, b) => nth(&[c, a, b]),
        Term::Match(s, arms) => match i {
            0 => Some(&**s),
            _ => arms.get(i - 1).map(|(_, b)| b),
        },
        Term::Fam { domain, body, .. } => nth(&[domain, body]),
        Term::Reindex { family, kf, vf, .. } => nth(&[family, kf, vf]),
        Term::Discard { family, sel } => nth(&[family, sel]),
        Term::Fold {
            family,
            op,
            identity,
            ..
        } => match identity {
            Some(id) => nth(&[family, op, id]),
            None => nth(&[family, op]),
        },
        Term::Fix {
            init, step, kind, ..
        } => match kind {
            FixKind::Lattice { join } => nth(&[init, step, join]),
            FixKind::Definedness => nth(&[init, step]),
        },
        Term::Gen {
            init, step, guard, ..
        } => nth(&[init, step, guard]),
        Term::Push(_, v) => nth(&[v]),
    }
}

/// Child `i` of `t`, in the order of [`child`], to change in place. A child behind an `Arc`
/// that other terms share is first copied (`Shared::make_mut`, which gives it a new id): that one node, with the children
/// it holds inline; its `Arc` children stay shared. `None` when `t` has no child `i`.
pub fn child_mut(t: &mut Term, i: u32) -> Option<&mut Term> {
    let i = i as usize;
    fn pick<const N: usize>(ts: [&mut Shared; N], i: usize) -> Option<&mut Term> {
        ts.into_iter().nth(i).map(Shared::make_mut)
    }
    match t {
        Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => None,
        Term::Lam(_, body) => pick([body], i),
        Term::App(f, args) => match i {
            0 => Some(Shared::make_mut(f)),
            _ => args.get_mut(i - 1),
        },
        Term::Prim(_, args) => args.get_mut(i),
        Term::Let(_, e, body) => pick([e, body], i),
        Term::If(c, a, b) => pick([c, a, b], i),
        Term::Match(s, arms) => match i {
            0 => Some(Shared::make_mut(s)),
            _ => arms.get_mut(i - 1).map(|(_, b)| b),
        },
        Term::Fam { domain, body, .. } => pick([domain, body], i),
        Term::Reindex { family, kf, vf, .. } => pick([family, kf, vf], i),
        Term::Discard { family, sel } => pick([family, sel], i),
        Term::Fold {
            family,
            op,
            identity,
            ..
        } => match identity {
            Some(id) => pick([family, op, id], i),
            None => pick([family, op], i),
        },
        Term::Fix {
            init, step, kind, ..
        } => match kind {
            FixKind::Lattice { join } => pick([init, step, join], i),
            FixKind::Definedness => pick([init, step], i),
        },
        Term::Gen {
            init, step, guard, ..
        } => pick([init, step, guard], i),
        Term::Push(_, v) => pick([v], i),
    }
}
