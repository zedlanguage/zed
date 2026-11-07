//! Sets of literals, each an atom and whether it is taken, as treaps whose nodes are shared: the
//! blocks of a decision list (module `list`) and the atoms of an exclusive or (`Part::xor`).
//!
//! A node's priority is a hash of its literal, ties broken by the literal's order, so the
//! priorities are distinct and one set has one shape whatever order its literals were added
//! in. The nodes of a thread are kept in a table by literal and children, so one set is one
//! node: two sets are equal exactly when their roots are one node, and a set built in two
//! orders is found again. An insertion or removal rebuilds the path to the place it changes,
//! `O(log n)` nodes in expectation, each looked up in the table in `O(log N)`; the walks keep
//! stacks of their own, so a set of any shape is walked on a small stack.

use std::sync::Arc;
use std::sync::atomic::Ordering as Atomic;

use super::{Literal, NEXT, Owned, mix};

/// A literal: an atom and whether it is taken.
pub(in crate::types) type Key<A> = (A, bool);

/// A node of a set: its literal, and the sets of the literals before and after it.
pub(in crate::types) struct Set<A: Literal> {
    /// The node's id, unique among the nodes of the process.
    pub(super) id: u64,
    /// A hash of the set's literals, equal for equal sets.
    pub(super) digest: u64,
    prio: u64,
    pub(super) key: Key<A>,
    len: usize,
    pub(super) left: Tree<A>,
    pub(super) right: Tree<A>,
}

/// A set: the root, or `None` when empty.
pub(in crate::types) type Tree<A> = Option<Arc<Set<A>>>;

/// The nodes of a thread's sets, by literal and children's ids.
pub(in crate::types) type SetTable<A> = std::collections::BTreeMap<(Key<A>, u64, u64), Arc<Set<A>>>;

/// A set node's children are freed in a loop (module `deep`), as a diagram's cells are.
impl<A: Literal> Drop for Set<A> {
    fn drop(&mut self) {
        for c in [self.left.take(), self.right.take()].into_iter().flatten() {
            A::free(Owned::Set(c));
        }
    }
}

fn priority<A: Literal>(key: &Key<A>) -> u64 {
    mix(mix(13, key.0.digest()), u64::from(key.1))
}

/// Whether a node of literal `key` and priority `prio` stands above `n`.
fn above<A: Literal>(prio: u64, key: &Key<A>, n: &Set<A>) -> bool {
    (prio, key) > (n.prio, &n.key)
}

fn id<A: Literal>(t: Option<&Arc<Set<A>>>) -> u64 {
    t.map_or(0, |s| s.id)
}

/// The digest of a set, `t` its root.
pub(super) fn digest<A: Literal>(t: Option<&Arc<Set<A>>>) -> u64 {
    t.map_or(mix(14, 0), |s| s.digest)
}

/// The number of literals.
pub(super) fn len<A: Literal>(t: Option<&Arc<Set<A>>>) -> usize {
    t.map_or(0, |s| s.len)
}

/// The node of `key` over `left` and `right`, the one in the table if there is one.
fn make<A: Literal>(key: Key<A>, left: Tree<A>, right: Tree<A>) -> Arc<Set<A>> {
    let k = (key, id(left.as_ref()), id(right.as_ref()));
    if let Some(s) = A::table(|t| t.sets.get(&k).cloned()) {
        return s;
    }
    let (key, ..) = &k;
    let s = Arc::new(Set {
        id: NEXT.fetch_add(1, Atomic::Relaxed),
        digest: mix(
            mix(
                mix(15, key.0.digest() ^ u64::from(key.1)),
                digest(left.as_ref()),
            ),
            digest(right.as_ref()),
        ),
        prio: priority(key),
        key: key.clone(),
        len: 1 + len(left.as_ref()) + len(right.as_ref()),
        left,
        right,
    });
    A::table(|t| t.sets.insert(k, s.clone()));
    s
}

/// The set of the one literal `key`.
pub(super) fn single<A: Literal>(key: Key<A>) -> Arc<Set<A>> {
    make(key, None, None)
}

/// Whether `atom` is in the set, and the literal's `taken` if so.
pub(super) fn get<A: Literal>(t: Option<&Arc<Set<A>>>, atom: &A) -> Option<bool> {
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
pub(super) fn min<A: Literal>(t: &Arc<Set<A>>) -> &Key<A> {
    let mut n = t;
    while let Some(l) = &n.left {
        n = l;
    }
    &n.key
}

/// The set split into its literals before `key` and those after; `key` is not in it.
fn split<A: Literal>(t: Option<&Arc<Set<A>>>, key: &Key<A>) -> (Tree<A>, Tree<A>) {
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
fn rebuild<A: Literal>(path: Vec<(&Arc<Set<A>>, bool)>, mut node: Tree<A>) -> Tree<A> {
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
pub(super) fn insert<A: Literal>(t: Option<&Arc<Set<A>>>, key: Key<A>) -> Arc<Set<A>> {
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
pub(super) fn remove<A: Literal>(t: &Arc<Set<A>>, key: &Key<A>) -> Tree<A> {
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
pub(super) fn iter<A: Literal>(t: Option<&Arc<Set<A>>>) -> Iter<'_, A> {
    let mut it = Iter { stack: Vec::new() };
    it.descend(t);
    it
}

pub(super) struct Iter<'a, A: Literal> {
    stack: Vec<&'a Set<A>>,
}

impl<'a, A: Literal> Iter<'a, A> {
    fn descend(&mut self, mut t: Option<&'a Arc<Set<A>>>) {
        while let Some(n) = t {
            self.stack.push(n);
            t = n.left.as_ref();
        }
    }
}

impl<'a, A: Literal> Iterator for Iter<'a, A> {
    type Item = &'a Key<A>;
    fn next(&mut self) -> Option<&'a Key<A>> {
        let n = self.stack.pop()?;
        self.descend(n.right.as_ref());
        Some(&n.key)
    }
}

/// The union of two sets with no atom in common: the smaller's literals added to the larger.
pub(super) fn union<A: Literal>(x: &Arc<Set<A>>, y: &Arc<Set<A>>) -> Arc<Set<A>> {
    let (big, small) = if x.len >= y.len { (x, y) } else { (y, x) };
    let mut out = big.clone();
    for k in iter(Some(small)) {
        out = insert(Some(&out), k.clone());
    }
    out
}

/// The literals in exactly one of the two sets: each of the smaller's added to the larger, or
/// removed from it when there.
pub(super) fn symmetric<A: Literal>(x: &Tree<A>, y: &Tree<A>) -> Tree<A> {
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
pub(super) fn single_key<A: Literal>(t: &Arc<Set<A>>) -> Option<&Key<A>> {
    (t.len == 1).then_some(&t.key)
}
