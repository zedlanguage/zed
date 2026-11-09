//! Sets of literals, each an atom and whether it is taken, as treaps whose nodes are shared: the
//! blocks of a decision list (module `list`) and the atoms of an exclusive or (`Part::xor`).
//!
//! A node's priority is a hash of its literal, ties broken by the literal's order, so the
//! priorities are distinct and one set has one shape whatever order its literals were added
//! in. The live nodes of a thread are kept in a table by literal and children, so one set is
//! one node: two sets are equal exactly when their roots are one node, and a set built in two
//! orders is found again. The table holds each node weakly, and a node leaves it when it is
//! dropped (step TABLE-life). An insertion or removal rebuilds the path to the place it changes,
//! `O(log n)` nodes in expectation, each looked up in the table in `O(log N)`; the walks keep
//! stacks of their own, so a set of any shape is walked on a small stack.

use std::sync::Arc;
use std::sync::atomic::Ordering as Atomic;

use crate::types::bucket::{self, Bucket};
use crate::types::hash::mix;

/// The atoms of sets, each kind with its thread's table of set nodes. Every atom of a diagram
/// (`bdd::Literal`) is one; the module needs no more of the atoms, so it imports nothing of the
/// diagrams that hold its sets.
pub(in crate::types) trait Atom: Ord + Clone + 'static {
    /// Runs `f` on the thread's table of set nodes.
    fn sets<R>(f: impl FnOnce(&mut SetTable<Self>) -> R) -> R;
    /// Runs `f` on the thread's table of set nodes to remove a dropped node's entry; nothing is
    /// done while the thread is ending or the table is borrowed (`bdd::Literal::untable`).
    fn unsets(f: impl FnOnce(&mut SetTable<Self>));
    /// A hash of the atom, equal for equal atoms.
    fn digest(&self) -> u64;
    /// Drops a set node in the thread's loop of type parts (module `deep`).
    fn free_set(set: Arc<Set<Self>>);
}

/// The next node id. Cells, sets and expressions take their ids from one counter, so an id
/// names one node among them; ids key the maps of a walk, never addresses.
pub(super) static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(2);

/// A literal: an atom and whether it is taken.
pub(in crate::types) type Key<A> = (A, bool);

/// A node of a set: its literal, and the sets of the literals before and after it.
pub(in crate::types) struct Set<A: Atom> {
    /// The node's id, unique among the nodes of the process.
    pub(in crate::types) id: u64,
    /// A hash of the set's literals, equal for equal sets.
    pub(in crate::types) digest: u64,
    prio: u64,
    /// The node's slot in its bucket of the table (module `bucket`).
    slot: u32,
    pub(in crate::types) key: Key<A>,
    len: usize,
    pub(in crate::types) left: Tree<A>,
    pub(in crate::types) right: Tree<A>,
}

/// A set: the root, or `None` when empty.
pub(in crate::types) type Tree<A> = Option<Arc<Set<A>>>;

/// The live nodes of a thread's sets, by the hash of the atom, whether it is taken and the
/// children's ids; nodes whose atoms differ but share a hash share a bucket, ordered by their
/// atoms (module `bucket`), and a lookup tells them apart by the atoms' order. Hashed rather than ordered by literal, since the table is
/// never read in order: a lookup in a table ordered by literal compared its key with some
/// `log N` others, each by the atoms' contents (three types read through their nodes for a
/// morphism type), which had made half the cost of a search through nested morphism types
/// (EMPTY-morphism-diff-cost).
pub(in crate::types) type SetTable<A> = std::collections::HashMap<
    Slot,
    Bucket<Set<A>>,
    std::hash::BuildHasherDefault<crate::types::hash::KeyHasher>,
>;

/// The key of a node's bucket in its [`SetTable`]: the hash of its atom, whether the atom is
/// taken, and its children's ids.
type Slot = (u64, bool, u64, u64);

/// The bucket of the node of `key` over the children of ids `left` and `right`.
fn slot<A: Atom>(key: &Key<A>, left: u64, right: u64) -> Slot {
    (key.0.digest(), key.1, left, right)
}

/// A set node leaves its thread's table, and its children are freed in a loop (module `deep`),
/// as a diagram's cells are.
impl<A: Atom> Drop for Set<A> {
    fn drop(&mut self) {
        let k = slot(&self.key, id(self.left.as_ref()), id(self.right.as_ref()));
        A::unsets(|t: &mut SetTable<A>| {
            // The node has no entry when it was made on another thread.
            if let Some(bucket) = t.get_mut(&k) {
                bucket.leave(self.slot, self);
                if bucket.is_empty() {
                    t.remove(&k);
                }
            }
        });
        for c in [self.left.take(), self.right.take()].into_iter().flatten() {
            A::free_set(c);
        }
    }
}

fn priority<A: Atom>(key: &Key<A>) -> u64 {
    mix(mix(13, key.0.digest()), u64::from(key.1))
}

/// Whether a node of literal `key` and priority `prio` stands above `n`.
fn above<A: Atom>(prio: u64, key: &Key<A>, n: &Set<A>) -> bool {
    (prio, key) > (n.prio, &n.key)
}

fn id<A: Atom>(t: Option<&Arc<Set<A>>>) -> u64 {
    t.map_or(0, |s| s.id)
}

/// The digest of a set, `t` its root.
pub(super) fn digest<A: Atom>(t: Option<&Arc<Set<A>>>) -> u64 {
    t.map_or(mix(14, 0), |s| s.digest)
}

/// The number of literals.
pub(super) fn len<A: Atom>(t: Option<&Arc<Set<A>>>) -> usize {
    t.map_or(0, |s| s.len)
}

/// The node of `key` over `left` and `right`, the one in the table if there is one.
fn make<A: Atom>(key: Key<A>, left: Tree<A>, right: Tree<A>) -> Arc<Set<A>> {
    let k = slot(&key, id(left.as_ref()), id(right.as_ref()));
    // No comparison or drop runs while the table is borrowed (module `bucket`); a bucket nearly
    // always holds one node at most.
    let bucket = |f: &mut dyn FnMut(&mut Bucket<Set<A>>)| A::sets(|t| f(t.entry(k).or_default()));
    let place = match bucket::find(bucket, |s| s.key.0.cmp(&key.0)) {
        Ok(s) => return s,
        Err(place) => place,
    };
    let s = Arc::new(Set {
        id: NEXT.fetch_add(1, Atomic::Relaxed),
        digest: mix(
            mix(mix(15, k.0 ^ u64::from(key.1)), digest(left.as_ref())),
            digest(right.as_ref()),
        ),
        prio: priority(&key),
        slot: place.slot(),
        key,
        len: 1 + len(left.as_ref()) + len(right.as_ref()),
        left,
        right,
    });
    bucket(&mut |b| b.insert(&place, Arc::downgrade(&s)));
    s
}

/// The set of the one literal `key`.
pub(super) fn single<A: Atom>(key: Key<A>) -> Arc<Set<A>> {
    make(key, None, None)
}

/// Whether `atom` is in the set, and the literal's `taken` if so.
pub(super) fn get<A: Atom>(t: Option<&Arc<Set<A>>>, atom: &A) -> Option<bool> {
    let mut cur = t;
    while let Some(n) = cur {
        cur = match atom.cmp(&n.key.0) {
            std::cmp::Ordering::Less => n.left.as_ref(),
            std::cmp::Ordering::Greater => n.right.as_ref(),
            std::cmp::Ordering::Equal => return Some(n.key.1),
        };
    }
    None
}

/// The smallest literal.
pub(super) fn min<A: Atom>(t: &Arc<Set<A>>) -> &Key<A> {
    let mut n = t;
    while let Some(l) = &n.left {
        n = l;
    }
    &n.key
}

/// The set split into its literals before `key` and those after; `key` is not in it.
fn split<A: Atom>(t: Option<&Arc<Set<A>>>, key: &Key<A>) -> (Tree<A>, Tree<A>) {
    let (mut lefts, mut rights) = (Vec::new(), Vec::new());
    let mut cur = t;
    while let Some(n) = cur {
        if n.key < *key {
            lefts.push(n);
            cur = n.right.as_ref();
        } else {
            rights.push(n);
            cur = n.left.as_ref();
        }
    }
    let mut l = None;
    for n in lefts.into_iter().rev() {
        l = Some(make(n.key.clone(), n.left.clone(), l));
    }
    let mut r = None;
    for n in rights.into_iter().rev() {
        r = Some(make(n.key.clone(), r, n.right.clone()));
    }
    (l, r)
}

/// The set with the nodes of `path` rebuilt over `node`, the last of `path` its parent; each
/// entry says whether the child is the node's left.
fn rebuild<A: Atom>(path: Vec<(&Arc<Set<A>>, bool)>, mut node: Tree<A>) -> Tree<A> {
    for (n, left) in path.into_iter().rev() {
        node = Some(if left {
            make(n.key.clone(), node, n.right.clone())
        } else {
            make(n.key.clone(), n.left.clone(), node)
        });
    }
    node
}

/// The set with `key` added; its atom is not in the set.
pub(super) fn insert<A: Atom>(t: Option<&Arc<Set<A>>>, key: Key<A>) -> Arc<Set<A>> {
    let prio = priority(&key);
    let mut path = Vec::new();
    let mut cur = t;
    while let Some(n) = cur {
        if above(prio, &key, n) {
            break;
        }
        let left = key < n.key;
        path.push((n, left));
        cur = if left {
            n.left.as_ref()
        } else {
            n.right.as_ref()
        };
    }
    let (l, r) = split(cur, &key);
    rebuild(path, Some(make(key, l, r))).expect("a set with a literal added has a root")
}

/// The set without `key`, which is in it.
pub(super) fn remove<A: Atom>(t: &Arc<Set<A>>, key: &Key<A>) -> Tree<A> {
    let mut path = Vec::new();
    let mut n = t;
    loop {
        let left = match key.cmp(&n.key) {
            std::cmp::Ordering::Equal => break,
            c => c.is_lt(),
        };
        path.push((n, left));
        n = (if left {
            n.left.as_ref()
        } else {
            n.right.as_ref()
        })
        .expect("the literal removed is in the set");
    }
    // The two children merged, the higher root of the two first, down one spine.
    let (mut a, mut b) = (n.left.as_ref(), n.right.as_ref());
    let mut spine: Vec<(&Arc<Set<A>>, bool)> = Vec::new();
    let bottom = loop {
        match (a, b) {
            (None, x) | (x, None) => break x.cloned(),
            (Some(x), Some(y)) => {
                if above(x.prio, &x.key, y) {
                    spine.push((x, false));
                    a = x.right.as_ref();
                } else {
                    spine.push((y, true));
                    b = y.left.as_ref();
                }
            }
        }
    };
    rebuild(path, rebuild(spine, bottom))
}

/// The literals in order, from a stack.
pub(super) fn iter<A: Atom>(t: Option<&Arc<Set<A>>>) -> Iter<'_, A> {
    let mut it = Iter { stack: Vec::new() };
    it.descend(t);
    it
}

pub(super) struct Iter<'a, A: Atom> {
    stack: Vec<&'a Set<A>>,
}

impl<'a, A: Atom> Iter<'a, A> {
    fn descend(&mut self, mut t: Option<&'a Arc<Set<A>>>) {
        while let Some(n) = t {
            self.stack.push(n);
            t = n.left.as_ref();
        }
    }
}

impl<'a, A: Atom> Iterator for Iter<'a, A> {
    type Item = &'a Key<A>;
    fn next(&mut self) -> Option<&'a Key<A>> {
        let n = self.stack.pop()?;
        self.descend(n.right.as_ref());
        Some(&n.key)
    }
}

/// The union of two sets with no atom in common: the smaller's literals added to the larger.
pub(super) fn union<A: Atom>(x: &Arc<Set<A>>, y: &Arc<Set<A>>) -> Arc<Set<A>> {
    let (big, small) = if x.len >= y.len { (x, y) } else { (y, x) };
    let mut out = big.clone();
    for k in iter(Some(small)) {
        out = insert(Some(&out), k.clone());
    }
    out
}

/// The literals in exactly one of the two sets: each of the smaller's added to the larger, or
/// removed from it when there.
pub(super) fn symmetric<A: Atom>(x: &Tree<A>, y: &Tree<A>) -> Tree<A> {
    let (big, small) = if len(x.as_ref()) >= len(y.as_ref()) {
        (x, y)
    } else {
        (y, x)
    };
    let mut out = big.clone();
    for k in iter(small.as_ref()) {
        out = match &out {
            Some(o) if get(Some(o), &k.0) == Some(k.1) => remove(o, k),
            _ => Some(insert(out.as_ref(), k.clone())),
        };
    }
    out
}

/// The one literal of a set of one.
pub(super) fn single_key<A: Atom>(t: &Arc<Set<A>>) -> Option<&Key<A>> {
    (t.len == 1).then_some(&t.key)
}

/// Whether two sets have the same literals. Equal sets made on one thread are one node, so
/// their ids agree; equal sets made on two threads are not (each thread has its table), so
/// trees of one digest are walked side by side, from a stack, past each pair of subtrees that
/// is one node. A set has one shape, its priorities a hash of its literals, so equal sets
/// match node by node (item XOR-cross-thread).
// Complexity tradeoff: two equal sets made on two threads are compared in `O(k)` for their `k`
// literals at each comparison, rather than made one node by a table of the process, which
// would take a lock at each set node made on every thread; on one thread the ids decide.
pub(super) fn same<A: Atom>(x: &Arc<Set<A>>, y: &Arc<Set<A>>) -> bool {
    let mut stack = vec![(x, y)];
    while let Some((x, y)) = stack.pop() {
        if x.id == y.id {
            continue;
        }
        if x.digest != y.digest || x.len != y.len || x.key != y.key {
            return false;
        }
        for (a, b) in [(&x.left, &y.left), (&x.right, &y.right)] {
            match (a, b) {
                (Some(a), Some(b)) => stack.push((a, b)),
                (None, None) => {}
                _ => return false,
            }
        }
    }
    true
}
