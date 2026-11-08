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

use crate::term::{FixKind, Shared, Term};
use crate::value::{Family, Id};
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
        let members = match v.errs() {
            Some(set) => set.keys().map(|m| (m, None)).collect(),
            None => BTreeMap::from([(v, None)]),
        };
        let mut held = Held {
            members,
            sets: HashMap::new(),
            tallies: HashMap::new(),
            seen: HashSet::new(),
            done: HashMap::new(),
            made: HashMap::new(),
            nodes: HashMap::new(),
            last: 0,
        };
        // The sets are found oldest fact first, over the facts `i` reaches by its inputs, each
        // taken once: a family's set is then found after that of the family it was made from,
        // and from it, by what was added ([`Held::base`]), so the two share their nodes and the
        // meets below are read from their differences. Newest first, a set found before the
        // set it was made from is read entry by entry and shares no nodes with it.
        // Complexity tradeoff: this reads the values of every fact `i` reaches, where the pass
        // below reads only the inputs of facts that hold a member, so a failure read next to a
        // large value holding none now costs that value's distinct parts, `O(m log m)` for `m`
        // parts, at most the work of the run that made them (a table of 64,000 entries beside
        // `#late`: 22 ms, against 0.01 ms before and 340 ms for the run). In exchange, a chain
        // of sets each one failure larger than the last costs `O(n log n)`, not `O(n²)`
        // (COMPLEXITY.md K25).
        let mut reached = vec![i];
        let mut taken = HashSet::from([i]);
        let mut next = 0;
        while let Some(&j) = reached.get(next) {
            next += 1;
            reached.extend(self.facts[j].inputs.iter().filter(|k| taken.insert(**k)));
        }
        reached.sort_unstable();
        for k in reached {
            if let Some(v) = &self.facts[k].value {
                held.of(v);
            }
        }
        // One backward pass over the facts, newest first: a fact's inputs completed before it,
        // so every fact that reaches `j` is taken before `j`. `traced[j]` holds the members
        // whose search reaches fact `j`; the search of member `m` goes on to each input that
        // holds `m`, and `j` is an origin of `m` when no input holds it. The sets are
        // persistent maps, and a set found from another shares its nodes, so the common
        // members of two sets are read from their difference when it is short: along a chain
        // of products, each holding one member more than the last, a step costs `O(log n)`.
        let mut traced: BTreeMap<usize, Found> = BTreeMap::from([(i, held.of(v).found)]);
        let mut out = BTreeSet::new();
        let mut last = Meet::default();
        while let Some((j, at_j)) = traced.pop_last() {
            let mut found = Found::new();
            for &k in &self.facts[j].inputs {
                debug_assert!(k < j, "a fact reads only facts completed before it");
                let Some(v) = &self.facts[k].value else {
                    continue;
                };
                let common = last.of(&at_j, held.of(v).found);
                if !common.is_empty() {
                    // An input that holds every member of `j` leaves none to `j`.
                    found = match found.len() == at_j.len() || common.len() == at_j.len() {
                        true => at_j.clone(),
                        false => join(&found, &common),
                    };
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

/// A set of failures; the values mean nothing.
type Found<'a> = OrdMap<&'a Value, ()>;

/// A set of failures with an id: two sets with one id hold the same failures, so the entries of
/// a family that hold one set are counted as one set, however many they are. The empty set's
/// id is 0. An id is drawn from [`Held::last`] in the order the walk finds sets, and is only
/// tested for equality: nothing in the result depends on its value.
#[derive(Clone, Default)]
struct Set<'a> {
    id: u64,
    found: Found<'a>,
}

/// How the set with some id is counted: as the failures of the set `base` (0 for none) and those
/// of `delta`, which holds none of the base's. A set made from another by adding failures is
/// counted from it, and a set from which another is made by removing failures is counted from
/// that one, so that a chain of sets each one failure larger than the last costs one failure
/// per set, whichever end of the chain is found first. Each base is smaller than the set on it,
/// so following bases ends.
#[derive(Clone)]
struct Node<'a> {
    base: u64,
    delta: Found<'a>,
}

/// A set counted in a [`Tally`]: its base and delta when it was counted, and the number of
/// counted sets whose base it is.
#[derive(Clone)]
struct Counted<'a> {
    base: u64,
    delta: Found<'a>,
    above: u32,
}

/// The failures a family's entries hold, counted so that the family's set can be found from
/// another family's by the difference of the two: entries added, removed or changed. A set an
/// entry holds is counted with its base, and the base's base, down to a set already counted,
/// and each counted set counts only its delta. So an entry that holds a set some other entry
/// holds costs `O(log n)`, and an entry whose set is made from a counted one costs the
/// failures it adds. The first set counted in an empty tally is counted whole, without its
/// bases and without a count for each failure: it holds each of its failures once, read from
/// its own map. So a family of one entry costs `O(log n)` however large the entry's set, and
/// only a later set none of whose bases is counted costs its size.
#[derive(Clone, Default)]
struct Tally<'a> {
    /// The id of each distinct non-empty set the entries hold, with the number of entries that
    /// hold it.
    entries: OrdMap<u64, u32>,
    /// The sets counted: those the entries hold and their bases.
    counted: OrdMap<u64, Counted<'a>>,
    /// The id of the set counted whole, 0 for none. Its delta is all of its failures, and
    /// they are not in `sets`.
    whole: u64,
    /// Each failure, with the number of counted sets other than `whole` whose delta holds it.
    sets: OrdMap<&'a Value, u32>,
    /// The failures: those of `whole` and the keys of `sets`.
    found: Found<'a>,
}

impl<'a> Tally<'a> {
    /// One more entry holds `s`.
    fn enter(&mut self, s: &Set<'a>, nodes: &HashMap<u64, Node<'a>>) {
        if s.found.is_empty() {
            return;
        }
        let n = self.entries.get(&s.id).copied().unwrap_or(0);
        self.entries.insert(s.id, n + 1);
        if n > 0 || self.counted.contains_key(&s.id) {
            return;
        }
        if self.counted.is_empty() {
            self.whole = s.id;
            self.found = s.found.clone();
            self.counted.insert(
                s.id,
                Counted {
                    base: 0,
                    delta: s.found.clone(),
                    above: 0,
                },
            );
            return;
        }
        // `found` takes the nodes it shares with `s`, so that later sets made from either are
        // compared by their difference.
        self.found = join(&self.found, &s.found);
        self.count(s.id, nodes);
    }

    /// Counts the set `id`, not counted, and its bases down to one that is.
    fn count(&mut self, mut id: u64, nodes: &HashMap<u64, Node<'a>>) {
        let mut above = 0;
        loop {
            let node = &nodes[&id];
            for x in node.delta.keys() {
                let k = self.sets.get(x).copied().unwrap_or(0);
                self.sets.insert(x, k + 1);
            }
            self.counted.insert(
                id,
                Counted {
                    base: node.base,
                    delta: node.delta.clone(),
                    above,
                },
            );
            if node.base == 0 {
                return;
            }
            if let Some(b) = self.counted.get_mut(&node.base) {
                b.above += 1;
                return;
            }
            (id, above) = (node.base, 1);
        }
    }

    /// One entry fewer holds `s`.
    fn leave(&mut self, s: &Set<'a>) {
        if s.found.is_empty() {
            return;
        }
        let n = self.entries[&s.id];
        if n > 1 {
            self.entries.insert(s.id, n - 1);
            return;
        }
        self.entries.remove(&s.id);
        if self.counted[&s.id].above == 0 {
            self.uncount(s.id);
        }
    }

    /// Removes the set `id`, which no entry holds and no counted set has as its base, and each
    /// base left in the same state.
    fn uncount(&mut self, mut id: u64) {
        loop {
            let c = self.counted.remove(&id).expect("a counted set");
            if id == self.whole {
                self.whole = 0;
                match self.counted.is_empty() {
                    true => self.found = Found::new(),
                    false => c.delta.keys().for_each(|x| self.drop_if_uncounted(x)),
                }
            } else {
                c.delta.keys().for_each(|x| self.less(x));
            }
            if c.base == 0 {
                return;
            }
            let b = self.counted.get_mut(&c.base).expect("a counted base");
            b.above -= 1;
            if b.above > 0 || self.entries.contains_key(&c.base) {
                return;
            }
            id = c.base;
        }
    }

    /// An entry that held `old` holds `new`. When `old` leaves the family and `new` enters
    /// it, `new` can be counted on `old`'s base with `old`'s delta changed by the difference
    /// of the two sets, when every failure it removes is in that delta: the counts change only
    /// at the failures the difference lists. That is done when the difference is shorter than
    /// the delta counting `new` from its own base would add, so a step costs the lesser.
    fn swap(&mut self, old: &Set<'a>, new: &Set<'a>, nodes: &HashMap<u64, Node<'a>>) {
        if old.id == new.id {
            return;
        }
        let leaves = !old.found.is_empty()
            && self.entries.get(&old.id) == Some(&1)
            && self.counted[&old.id].above == 0;
        let enters = !new.found.is_empty() && !self.counted.contains_key(&new.id);
        if leaves && enters && self.swap_by_difference(old, new, nodes) {
            return;
        }
        // `new` first: a set made from `old` is then counted on it.
        self.enter(new, nodes);
        self.leave(old);
    }

    /// [`Tally::swap`] by the difference of `old` and `new`; false, with nothing changed, when
    /// it is not shorter than counting `new` or removes a failure of `old`'s base.
    fn swap_by_difference(
        &mut self,
        old: &Set<'a>,
        new: &Set<'a>,
        nodes: &HashMap<u64, Node<'a>>,
    ) -> bool {
        let node = &nodes[&new.id];
        let limit = match self.counted.contains_key(&node.base) {
            true => node.delta.len(),
            false => new.found.len(),
        };
        let mut diff = Vec::new();
        for d in old.found.diff(&new.found) {
            if diff.len() >= limit {
                return false;
            }
            diff.push(d);
        }
        let was = &self.counted[&old.id];
        let removes_base = diff.iter().any(|d| match d {
            DiffItem::Remove(x, _) => !was.delta.contains_key(*x),
            _ => false,
        });
        if removes_base {
            return false;
        }
        let Counted {
            base, mut delta, ..
        } = self.counted.remove(&old.id).expect("counted");
        self.entries.remove(&old.id);
        self.entries.insert(new.id, 1);
        if old.id == self.whole {
            // The set counted whole becomes `new`, read from its own map, before the failures
            // `old` held and `new` does not are tested against it.
            self.whole = new.id;
            self.counted.insert(
                new.id,
                Counted {
                    base: 0,
                    delta: new.found.clone(),
                    above: 0,
                },
            );
            for d in diff {
                match d {
                    DiffItem::Add(x, _) => {
                        self.found.insert(x, ());
                    }
                    DiffItem::Remove(x, _) => self.drop_if_uncounted(x),
                    DiffItem::Update { .. } => {}
                }
            }
            return true;
        }
        for d in diff {
            match d {
                DiffItem::Add(x, _) => {
                    delta.insert(*x, ());
                    self.more(x);
                }
                DiffItem::Remove(x, _) => {
                    delta.remove(*x);
                    self.less(x);
                }
                DiffItem::Update { .. } => {}
            }
        }
        self.counted.insert(
            new.id,
            Counted {
                base,
                delta,
                above: 0,
            },
        );
        true
    }

    /// Whether the set counted whole holds `x`.
    fn whole_holds(&self, x: &'a Value) -> bool {
        self.whole != 0 && self.counted[&self.whole].delta.contains_key(x)
    }

    /// `x` leaves `found` unless a counted set's delta holds it.
    fn drop_if_uncounted(&mut self, x: &'a Value) {
        if !self.sets.contains_key(x) && !self.whole_holds(x) {
            self.found.remove(x);
        }
    }

    /// One more counted set holds `x` in its delta.
    fn more(&mut self, x: &'a Value) {
        let n = self.sets.get(x).copied().unwrap_or(0);
        self.sets.insert(x, n + 1);
        if n == 0 {
            self.found.insert(x, ());
        }
    }

    /// One counted set fewer holds `x` in its delta.
    fn less(&mut self, x: &'a Value) {
        match self.sets[x] {
            1 => {
                self.sets.remove(x);
                self.drop_if_uncounted(x);
            }
            n => {
                self.sets.insert(x, n - 1);
            }
        }
    }
}

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
struct Held<'a> {
    /// Each failure, with the set a value equal to it holds once found.
    members: BTreeMap<&'a Value, Option<Set<'a>>>,
    sets: HashMap<Part, Set<'a>>,
    /// The tally of each family whose set is found, by the family's id.
    tallies: HashMap<Id, Tally<'a>>,
    /// The parts entered: a part is entered once, and its set is found before any part that
    /// holds it, since a value holds no part that holds it.
    seen: HashSet<Part>,
    /// The families whose sets are found, by id.
    done: HashMap<Id, &'a Family>,
    /// The families whose sets are found, by the id of the family each was made from.
    made: HashMap<Id, &'a Family>,
    /// How each set with a non-zero id is counted.
    nodes: HashMap<u64, Node<'a>>,
    /// The last id given to a set.
    last: u64,
}

impl<'a> Held<'a> {
    fn of(&mut self, v: &'a Value) -> Set<'a> {
        let mut todo = vec![Task::Enter(v)];
        while let Some(task) = todo.pop() {
            match task {
                Task::Enter(v) => self.enter(v, &mut todo),
                Task::Items(xs) => {
                    let mut s = Set::default();
                    for x in xs.iter() {
                        let r = self.read(x);
                        s = self.union(s, r);
                    }
                    self.sets.insert(Part::Items(xs.id()), s);
                }
                Task::Family(f, base) => {
                    let (tally, s) = self.family(f, base);
                    self.sets.insert(Part::Family(f.id()), s);
                    self.tallies.insert(f.id(), tally);
                    self.done.insert(f.id(), f);
                    if f.from() != 0 {
                        self.made.entry(f.from()).or_insert(f);
                    }
                }
            }
        }
        self.read(v)
    }

    /// A new set of the failures `found`, counted as those of the set `base` and `delta`.
    fn fresh(&mut self, base: u64, delta: Found<'a>, found: Found<'a>) -> Set<'a> {
        self.last += 1;
        self.nodes.insert(self.last, Node { base, delta });
        Set {
            id: self.last,
            found,
        }
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
    /// two families that share no nodes compares the values at each common key. Those values
    /// are compared shallowly ([`Family::shallow_diff`]): a family made from another by a
    /// change `d` levels down differs from it at each of those levels, and reading the two down
    /// to their difference at each level cost `O(d²)` per change.
    fn base(&self, f: &'a Family) -> Option<FromBase<'a>> {
        let base = match self.done.get(&f.from()) {
            Some(base) if f.from() != 0 => *base,
            _ => *self.made.get(&f.id())?,
        };
        Some((base, base.shallow_diff(f, f.len())?))
    }

    /// The tally and the set of `f`. Entries that hold one set are counted once, and a set
    /// made from a counted one costs what it adds, so the work is the number of entries read,
    /// `O(log n)` each, and the deltas of the sets that enter or leave the tally.
    fn family(&mut self, f: &'a Family, base: Option<FromBase<'a>>) -> (Tally<'a>, Set<'a>) {
        let (tally, was) = match base {
            None => {
                let mut t = Tally::default();
                for e in f.0.values() {
                    let s = self.read(e);
                    t.enter(&s, &self.nodes);
                }
                (t, None)
            }
            Some((base, diff)) => {
                let mut t = self.tallies[&base.id()].clone();
                for d in diff {
                    match d {
                        DiffItem::Add(_, e) => {
                            let s = self.read(e);
                            t.enter(&s, &self.nodes);
                        }
                        DiffItem::Remove(_, e) => t.leave(&self.read(e)),
                        DiffItem::Update { old, new } => {
                            let (old, new) = (self.read(old.1), self.read(new.1));
                            t.swap(&old, &new, &self.nodes);
                        }
                    }
                }
                (t, Some(self.sets[&Part::Family(base.id())].clone()))
            }
        };
        // The set keeps an id it equals: that of the one distinct set the entries hold, or the
        // base's when the failures are the base's map itself.
        let found = tally.found.clone();
        let set = match (tally.entries.len(), was) {
            _ if found.is_empty() => Set::default(),
            (1, _) => Set {
                id: *tally.entries.keys().next().expect("one set"),
                found,
            },
            (_, Some(was)) if was.found.ptr_eq(&found) => was,
            (_, Some(was)) => self.made_by_difference(was, found),
            (_, None) => self.fresh(0, found.clone(), found),
        };
        (tally, set)
    }

    /// A new set of the failures `found`, which a family's tally found from the set `was` of the
    /// family it was made from, or of one made from it. When `found` only adds failures to
    /// `was`, it is counted on `was`; when it only removes some, `was` is counted on it from
    /// then on, if that makes `was`'s delta smaller. The difference costs what the tally
    /// changed, since the two maps share the rest.
    fn made_by_difference(&mut self, was: Set<'a>, found: Found<'a>) -> Set<'a> {
        let Some(diff) = short_diff(&was.found, &found) else {
            return self.fresh(0, found.clone(), found);
        };
        let mut adds = Found::new();
        let mut removes = Found::new();
        for d in diff {
            match d {
                DiffItem::Add(x, _) => adds.insert(*x, ()),
                DiffItem::Remove(x, _) => removes.insert(*x, ()),
                DiffItem::Update { .. } => None,
            };
        }
        match (adds.is_empty(), removes.is_empty()) {
            (false, true) => self.fresh(was.id, adds, found),
            (true, false) => {
                let set = self.fresh(0, found.clone(), found);
                let node = self.nodes.get_mut(&was.id).expect("a node for each set");
                if removes.len() < node.delta.len() {
                    *node = Node {
                        base: set.id,
                        delta: removes,
                    };
                }
                set
            }
            (true, true) => was,
            (false, false) => self.fresh(0, found.clone(), found),
        }
    }

    /// The set of `a` and `b` together, with the id of the larger when the smaller adds
    /// nothing to it, and otherwise counted on the larger.
    fn union(&mut self, a: Set<'a>, b: Set<'a>) -> Set<'a> {
        let (large, small) = match a.found.len() >= b.found.len() {
            true => (a, b),
            false => (b, a),
        };
        if small.found.is_empty() || small.id == large.id {
            return large;
        }
        let added: Found<'a> = match short_diff(&large.found, &small.found) {
            Some(diff) => diff
                .into_iter()
                .filter_map(|d| match d {
                    DiffItem::Add(x, _) => Some((*x, ())),
                    _ => None,
                })
                .collect(),
            None => small
                .found
                .keys()
                .filter(|x| !large.found.contains_key(*x))
                .map(|x| (*x, ()))
                .collect(),
        };
        if added.is_empty() {
            return large;
        }
        let mut found = large.found.clone();
        for x in added.keys() {
            found.insert(*x, ());
        }
        self.fresh(large.id, added, found)
    }

    /// The set of `v`, the sets of its parts found. A value equal to a member holds that
    /// member too; its set is found once and kept, so that each read of it has one id.
    fn read(&mut self, v: &'a Value) -> Set<'a> {
        let items = |xs: &Items| match xs.is_empty() {
            true => Set::default(),
            false => self.sets[&Part::Items(xs.id())].clone(),
        };
        let s = match v {
            Value::Atom(a) => items(&a.args),
            Value::Tuple(xs) | Value::Path(xs) => items(xs),
            Value::Family(f) if !f.is_empty() => self.sets[&Part::Family(f.id())].clone(),
            _ => Set::default(),
        };
        let Some((&m, own)) = self.members.range_mut::<&Value, _>(v..=v).next() else {
            return s;
        };
        if let Some(own) = own {
            return own.clone();
        }
        let own_set = match s.found.contains_key(m) {
            true => s,
            false => {
                // [`Held::fresh`] by hand: `own` borrows `members`.
                self.last += 1;
                let delta = Found::unit(m, ());
                self.nodes.insert(self.last, Node { base: s.id, delta });
                let mut found = s.found;
                found.insert(m, ());
                Set {
                    id: self.last,
                    found,
                }
            }
        };
        *own = Some(own_set.clone());
        own_set
    }
}

/// The difference from `from` to `to`, when it lists fewer items than the smaller set has.
fn short_diff<'s, 'a>(
    from: &'s Found<'a>,
    to: &'s Found<'a>,
) -> Option<Vec<DiffItem<'s, 's, &'a Value, ()>>> {
    diff_within(from, to, from.len().min(to.len()))
}

/// The difference from `from` to `to`, when it lists fewer than `limit` items. The work is the
/// items listed and the members both maps hold in nodes they do not share; the nodes they
/// share are skipped.
fn diff_within<'s, 'a>(
    from: &'s Found<'a>,
    to: &'s Found<'a>,
    limit: usize,
) -> Option<Vec<DiffItem<'s, 's, &'a Value, ()>>> {
    let mut diff = Vec::new();
    for d in from.diff(to) {
        if diff.len() >= limit {
            return None;
        }
        diff.push(d);
    }
    Some(diff)
}

/// The last meet taken in [`Provenance::origins`]: the failures in both `a` and `b`. The next
/// meet with the same first set is also found from it, by the difference of the second sets:
/// a fact that reads one input after another, each holding one member more than the last
/// (the bindings of a chain of `let`s, read by the facts of the `let`s, which hold all the
/// members of the result), then costs `O(log n)` an input, where meeting each input anew costs
/// its size.
#[derive(Default)]
struct Meet<'a> {
    a: Found<'a>,
    b: Found<'a>,
    common: Found<'a>,
}

impl<'a> Meet<'a> {
    /// The failures in both `a` and `b`, kept for the next meet unless `a` is `b`.
    fn of(&mut self, a: &Found<'a>, b: Found<'a>) -> Found<'a> {
        if a.ptr_eq(&b) {
            return b;
        }
        // A meet equal to either set is that set, so that it shares the set's nodes and later
        // joins and meets with sets made from it are read from their differences.
        let common = match self.find(a, &b) {
            c if c.len() == b.len() => b.clone(),
            c if c.len() == a.len() => a.clone(),
            c => c,
        };
        *self = Meet {
            a: a.clone(),
            b,
            common: common.clone(),
        };
        common
    }

    /// The failures in both `a` and `b`, from the shorter of two differences: that of the
    /// smaller set to the larger, which lists what is only in the smaller, and, when `a` is the
    /// last meet's first set, that of the last second set to `b`. The two are read a step of
    /// each in turn, each to fewer items than the smaller set has, so the work is
    /// `O(log n)` for each item of the shorter; when neither is that short, each member of the
    /// smaller set is looked up in the larger. The work is `O(min(|a|, |b|) log n)` at most.
    fn find(&self, a: &Found<'a>, b: &Found<'a>) -> Found<'a> {
        let (small, large) = match a.len() <= b.len() {
            true => (a, b),
            false => (b, a),
        };
        let limit = small.len();
        let mut direct = Some(Bounded::new(small.diff(large), limit));
        let mut again = self
            .a
            .ptr_eq(a)
            .then(|| Bounded::new(self.b.diff(b), limit));
        while direct.is_some() || again.is_some() {
            if let Some(d) = &mut direct {
                match d.step() {
                    Read::Ended => {
                        let mut out = small.clone();
                        for d in std::mem::take(&mut d.items) {
                            if let DiffItem::Remove(x, _) = d {
                                out.remove(x);
                            }
                        }
                        return out;
                    }
                    Read::Over => direct = None,
                    Read::More => {}
                }
            }
            if let Some(d) = &mut again {
                match d.step() {
                    Read::Ended => {
                        let mut out = self.common.clone();
                        for d in std::mem::take(&mut d.items) {
                            match d {
                                DiffItem::Add(x, _) if a.contains_key(*x) => {
                                    out.insert(*x, ());
                                }
                                DiffItem::Remove(x, _) => {
                                    out.remove(*x);
                                }
                                _ => {}
                            }
                        }
                        return out;
                    }
                    Read::Over => again = None,
                    Read::More => {}
                }
            }
        }
        small
            .keys()
            .filter(|x| large.contains_key(*x))
            .map(|x| (*x, ()))
            .collect()
    }
}

/// A difference of two sets, read an item at a time up to a limit.
struct Bounded<I: Iterator> {
    diff: I,
    items: Vec<I::Item>,
    limit: usize,
}

/// What reading one more item of a [`Bounded`] difference found.
enum Read {
    /// The difference ended within the limit; its items are all read.
    Ended,
    /// It lists the limit or more items.
    Over,
    /// An item was read.
    More,
}

impl<I: Iterator> Bounded<I> {
    /// `diff`, to be read to fewer than `limit` items.
    fn new(diff: I, limit: usize) -> Self {
        Bounded {
            diff,
            items: Vec::new(),
            limit,
        }
    }

    /// Reads one more item.
    fn step(&mut self) -> Read {
        match self.diff.next() {
            None => Read::Ended,
            Some(d) => {
                if self.items.len() >= self.limit {
                    return Read::Over;
                }
                self.items.push(d);
                Read::More
            }
        }
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
                if let DiffItem::Add(x, _) = d {
                    out.insert(*x, ());
                }
            }
        }
        None => {
            for x in small.keys() {
                if !out.contains_key(x) {
                    out.insert(*x, ());
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

#[cfg(test)]
mod tests {
    use super::*;

    /// The sets of `ids`, each with its base and the failures it adds, in an order that puts
    /// each base first; and the failures of each.
    struct Sets<'a> {
        nodes: HashMap<u64, Node<'a>>,
        sets: HashMap<u64, Set<'a>>,
    }

    impl<'a> Sets<'a> {
        fn new(atoms: &'a [Value], ids: &[(u64, u64, &[usize])]) -> Self {
            let mut out = Sets {
                nodes: HashMap::new(),
                sets: HashMap::new(),
            };
            for &(id, base, adds) in ids {
                let delta: Found = adds.iter().map(|&k| (&atoms[k], ())).collect();
                let mut found = match base {
                    0 => Found::new(),
                    b => out.sets[&b].found.clone(),
                };
                delta.keys().for_each(|x| {
                    found.insert(*x, ());
                });
                out.nodes.insert(id, Node { base, delta });
                out.sets.insert(id, Set { id, found });
            }
            out
        }
    }

    /// The failures of the sets the entries hold, as atom numbers.
    fn expected(atoms: &[Value], held: &[&Set]) -> Vec<usize> {
        let all: BTreeSet<&Value> = held.iter().flat_map(|s| s.found.keys().copied()).collect();
        (0..atoms.len())
            .filter(|&k| all.contains(&atoms[k]))
            .collect()
    }

    fn found(atoms: &[Value], t: &Tally) -> Vec<usize> {
        (0..atoms.len())
            .filter(|&k| t.found.contains_key(&atoms[k]))
            .collect()
    }

    #[test]
    fn a_tally_keeps_the_failures_of_its_entries_when_the_set_counted_whole_changes() {
        let atoms: Vec<Value> = (0..8).map(|k| Value::atom(&format!("a{k}"))).collect();
        // 1 = {0, 1, 2, 3}; 2 = {0, 1, 2, 4}, a set close to 1; 3 = {3, 5}; 4 = {6, 7}, far
        // from 1; 5 = 3 and {6}.
        let s = Sets::new(
            &atoms,
            &[
                (1, 0, &[0, 1, 2, 3]),
                (2, 0, &[0, 1, 2, 4]),
                (3, 0, &[3, 5]),
                (4, 0, &[6, 7]),
                (5, 3, &[6]),
            ],
        );
        let set = |id: u64| &s.sets[&id];
        let check = |t: &Tally, held: &[&Set], step: &str| {
            assert_eq!(found(&atoms, t), expected(&atoms, held), "{step}");
        };

        // The set counted whole leaves: the tally is empty, then another set is counted.
        let mut t = Tally::default();
        t.enter(set(1), &s.nodes);
        check(&t, &[set(1)], "enter 1");
        t.leave(set(1));
        check(&t, &[], "leave 1");
        t.enter(set(3), &s.nodes);
        check(&t, &[set(3)], "enter 3 after");

        // The set counted whole leaves while another holds one of its failures.
        let mut t = Tally::default();
        t.enter(set(1), &s.nodes);
        t.enter(set(3), &s.nodes);
        t.leave(set(1));
        check(&t, &[set(3)], "leave 1 under 3");

        // The set counted whole is replaced by one close to it, by their difference, while
        // another set holds the failure the difference removes.
        let mut t = Tally::default();
        t.enter(set(1), &s.nodes);
        t.enter(set(3), &s.nodes);
        t.swap(set(1), set(2), &s.nodes);
        check(&t, &[set(2), set(3)], "swap 1 for 2 under 3");
        t.leave(set(3));
        check(&t, &[set(2)], "leave 3");

        // The same, with no other set.
        let mut t = Tally::default();
        t.enter(set(1), &s.nodes);
        t.swap(set(1), set(2), &s.nodes);
        check(&t, &[set(2)], "swap 1 for 2");
        t.swap(set(2), set(4), &s.nodes);
        check(&t, &[set(4)], "swap 2 for 4");

        // The set counted whole is replaced by one far from it, and the sets counted on a base
        // come and go around it.
        let mut t = Tally::default();
        t.enter(set(1), &s.nodes);
        t.enter(set(5), &s.nodes);
        check(&t, &[set(1), set(5)], "enter 1 and 5");
        t.swap(set(1), set(4), &s.nodes);
        check(&t, &[set(4), set(5)], "swap 1 for 4 under 5");
        t.swap(set(5), set(3), &s.nodes);
        check(&t, &[set(4), set(3)], "swap 5 for 3");
        t.leave(set(4));
        check(&t, &[set(3)], "leave 4");
        t.leave(set(3));
        check(&t, &[], "leave 3 last");
    }
}
