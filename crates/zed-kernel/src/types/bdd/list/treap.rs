//! Persistent ordered maps as treaps with sizes, built from two operations, `split` and `join`
//! (Blelloch, Ferizovic and Sun, "Just join for parallel ordered sets", SPAA 2016, section 4 for
//! treaps; Sun, Ferizovic and Blelloch, "PAM: parallel augmented maps", PPoPP 2018, for the size
//! kept at each node): get, split, join, insertion, removal, the place of a key and the key at a
//! place, each `O(log n)` expected. Plan row KERNEL-bdd-rejoin-bytes: the index of a decision
//! list's blocks ([`super::Index`]).
//!
//! A map is shared, never changed: an operation makes new nodes along the paths it changes and
//! shares every subtree it leaves alone. A node's priority is a function of its key drawn at
//! random once per run ([`Keyed::priority`], module [`crate::priority`]), ties broken by the
//! order of the keys, so in a run the keys of a map fix its shape whatever order they came in.
//! Seidel and Aragon's bound on the expected depth, `O(log n)` for every set of keys, holds for
//! keys at distinct points of the draw (module [`crate::priority`]).
//!
//! Every walk keeps a stack of its own, and a map is dropped in a loop, so the stack needed does
//! not depend on a map's height.

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::sync::Arc;

/// A key of a treap: ordered, with a priority drawn once per run.
pub(super) trait Keyed: Ord + Clone {
    /// The key's priority: a random function of the key, one per use of the treap, drawn once
    /// per run (module [`crate::priority`]).
    fn priority(&self) -> u64;
}

/// A node: its key and value, the number of keys of its subtree, and the maps of the keys
/// before and after it.
pub(super) struct Node<K, V> {
    key: K,
    value: V,
    prio: u64,
    len: usize,
    left: Tree<K, V>,
    right: Tree<K, V>,
}

/// A map: its root, or `None` when empty.
pub(super) type Tree<K, V> = Option<Arc<Node<K, V>>>;

/// A map is freed in a loop, a node whose last handle goes handing its children on, so a map of
/// any height is dropped on a small stack.
impl<K, V> Drop for Node<K, V> {
    fn drop(&mut self) {
        // Only children whose last handle this is are walked; the stack allocates nothing
        // until one is, and a node popped from it has no children left when it drops.
        let mut stack: Vec<Node<K, V>> = Vec::new();
        let free = |c: Tree<K, V>, stack: &mut Vec<Node<K, V>>| {
            if let Some(c) = c
                && let Ok(n) = Arc::try_unwrap(c)
            {
                stack.push(n);
            }
        };
        free(self.left.take(), &mut stack);
        free(self.right.take(), &mut stack);
        while let Some(mut n) = stack.pop() {
            free(n.left.take(), &mut stack);
            free(n.right.take(), &mut stack);
        }
    }
}

/// Whether node `a` stands above node `b`: the higher priority, ties broken by the key.
fn above<K: Keyed, V>(a: &Node<K, V>, b: &Node<K, V>) -> bool {
    (a.prio, &a.key) > (b.prio, &b.key)
}

/// The node `n` made again over `left` and `right`, its priority kept rather than computed.
fn again<K: Clone, V: Clone>(
    n: &Node<K, V>,
    left: Tree<K, V>,
    right: Tree<K, V>,
) -> Arc<Node<K, V>> {
    Arc::new(Node {
        key: n.key.clone(),
        value: n.value.clone(),
        prio: n.prio,
        len: 1 + len(&left) + len(&right),
        left,
        right,
    })
}

/// The path `path` from the root down, each node with the side taken from it, made again over
/// `bottom`, the new subtree where the path ends.
fn up<K: Clone, V: Clone>(
    path: Vec<(&Arc<Node<K, V>>, bool)>,
    mut bottom: Tree<K, V>,
) -> Tree<K, V> {
    for (n, left) in path.into_iter().rev() {
        bottom = Some(match left {
            true => again(n, bottom, n.right.clone()),
            false => again(n, n.left.clone(), bottom),
        });
    }
    bottom
}

/// The number of keys.
pub(super) fn len<K, V>(t: &Tree<K, V>) -> usize {
    t.as_ref().map_or(0, |n| n.len)
}

/// The value of `key`, if the map has it: one walk down, `O(log n)`.
pub(super) fn get<'a, K: Borrow<Q>, Q: Ord + ?Sized, V>(
    t: &'a Tree<K, V>,
    key: &Q,
) -> Option<&'a V> {
    let mut cur = t.as_deref();
    while let Some(n) = cur {
        cur = match key.cmp(n.key.borrow()) {
            Ordering::Less => n.left.as_deref(),
            Ordering::Greater => n.right.as_deref(),
            Ordering::Equal => return Some(&n.value),
        };
    }
    None
}

/// The place of `key` in order (from 0), if the map has it: one walk down, the sizes of the left
/// subtrees passed to the right added, `O(log n)`.
pub(super) fn place<K: Ord, V>(t: &Tree<K, V>, key: &K) -> Option<usize> {
    let (mut cur, mut below) = (t.as_deref(), 0);
    while let Some(n) = cur {
        match key.cmp(&n.key) {
            Ordering::Less => cur = n.left.as_deref(),
            Ordering::Greater => {
                below += len(&n.left) + 1;
                cur = n.right.as_deref();
            }
            Ordering::Equal => return Some(below + len(&n.left)),
        }
    }
    None
}

/// The key at place `k` (from 0) in order; the map has more than `k` keys.
pub(super) fn nth<K, V>(t: &Tree<K, V>, mut k: usize) -> &K {
    let mut at = t.as_deref().expect("the map has the place asked for");
    loop {
        let ln = len(&at.left);
        match k.cmp(&ln) {
            Ordering::Less => at = at.left.as_deref().expect("the place is on the left"),
            Ordering::Equal => return &at.key,
            Ordering::Greater => {
                k -= ln + 1;
                at = at.right.as_deref().expect("the place is on the right");
            }
        }
    }
}

/// The entries in order, by one walk with a stack of its own.
#[cfg(test)]
pub(super) fn iter<K, V>(t: &Tree<K, V>) -> impl Iterator<Item = (&K, &V)> {
    let (mut stack, mut at) = (Vec::new(), t.as_deref());
    std::iter::from_fn(move || {
        while let Some(n) = at {
            stack.push(n);
            at = n.left.as_deref();
        }
        let n = stack.pop()?;
        at = n.right.as_deref();
        Some((&n.key, &n.value))
    })
}

/// The entries of `t` before `key` and those after it, `key`'s own left out: one walk down from
/// the root, the nodes passed made again on each side, `O(height)`.
fn split<K: Keyed + Borrow<Q>, Q: Ord + ?Sized, V: Clone>(
    t: &Tree<K, V>,
    key: &Q,
) -> (Tree<K, V>, Tree<K, V>) {
    let (mut lefts, mut rights) = (Vec::new(), Vec::new());
    let mut cur = t.as_ref();
    let (mut l, mut r) = (None, None);
    while let Some(n) = cur {
        match n.key.borrow().cmp(key) {
            Ordering::Less => {
                lefts.push(n);
                cur = n.right.as_ref();
            }
            Ordering::Greater => {
                rights.push(n);
                cur = n.left.as_ref();
            }
            Ordering::Equal => {
                (l, r) = (n.left.clone(), n.right.clone());
                break;
            }
        }
    }
    for n in lefts.into_iter().rev() {
        l = Some(again(n, n.left.clone(), l));
    }
    for n in rights.into_iter().rev() {
        r = Some(again(n, r, n.right.clone()));
    }
    (l, r)
}

/// The first `k` entries of `t`: one walk down by the sizes, the nodes passed on the left made
/// again, `O(height)`. A cut at either end leaves `t` whole or empty.
pub(super) fn prefix<K: Keyed, V: Clone>(t: &Tree<K, V>, k: usize) -> Tree<K, V> {
    if k >= len(t) {
        return t.clone();
    }
    let mut lefts = Vec::new();
    let (mut cur, mut k) = (t.as_ref(), k);
    while let Some(n) = cur {
        let ln = len(&n.left);
        if k <= ln {
            cur = n.left.as_ref();
        } else {
            lefts.push(n);
            k -= ln + 1;
            cur = n.right.as_ref();
        }
    }
    let mut l = None;
    for n in lefts.into_iter().rev() {
        l = Some(again(n, n.left.clone(), l));
    }
    l
}

/// The entries of `a` and of `b`, every key of `a` before every key of `b`: the two merged down
/// one spine, the higher root first, `O(height)`.
fn join<K: Keyed, V: Clone>(a: Tree<K, V>, b: Tree<K, V>) -> Tree<K, V> {
    let mut spine: Vec<(Arc<Node<K, V>>, bool)> = Vec::new();
    let (mut a, mut b) = (a, b);
    let mut bottom = loop {
        match (a, b) {
            (None, x) | (x, None) => break x,
            (Some(x), Some(y)) => {
                if above(&x, &y) {
                    a = x.right.clone();
                    b = Some(y);
                    spine.push((x, false));
                } else {
                    b = y.left.clone();
                    a = Some(x);
                    spine.push((y, true));
                }
            }
        }
    };
    for (n, left) in spine.into_iter().rev() {
        bottom = Some(match left {
            true => again(&n, bottom, n.right.clone()),
            false => again(&n, n.left.clone(), bottom),
        });
    }
    bottom
}

/// `t` with `key` set to `value`: one walk down while the nodes stand above the new one, then
/// the subtree there split at the key (or the key's own node given the new value), the path
/// made again, `O(log n)` expected.
///
/// Complexity tradeoff: an insertion by `split` and two `join`s (Blelloch, Ferizovic and Sun)
/// makes every node on the search path again and then the spines it joins, about three times
/// the nodes; this walk (Seidel and Aragon's insertion, without rotations) makes the path above
/// the new node and splits only the subtree below it, whose two spines have `O(1)` nodes in
/// expectation. The shape is the same, since a treap's shape is fixed by its keys.
pub(super) fn insert<K: Keyed, V: Clone>(t: &Tree<K, V>, key: K, value: V) -> Tree<K, V> {
    let prio = key.priority();
    let mut path = Vec::new();
    let mut cur = t.as_ref();
    // A node of the path stands above the new one: a node of the same key has its priority, so
    // the walk stops there, the key's node being below every node above the new one.
    while let Some(n) = cur
        && (n.prio, &n.key) > (prio, &key)
    {
        let left = key < n.key;
        path.push((n, left));
        cur = if left {
            n.left.as_ref()
        } else {
            n.right.as_ref()
        };
    }
    let bottom = match cur {
        Some(n) if n.key == key => Arc::new(Node {
            key,
            value,
            prio,
            len: n.len,
            left: n.left.clone(),
            right: n.right.clone(),
        }),
        _ => {
            let (l, r) = split(&cur.cloned(), &key);
            Arc::new(Node {
                len: 1 + len(&l) + len(&r),
                key,
                value,
                prio,
                left: l,
                right: r,
            })
        }
    };
    up(path, Some(bottom))
}

/// `t` without `key`: one walk down to its node, whose two subtrees are joined in its place, the
/// path made again, `O(log n)` expected (the joined spines have `O(1)` nodes in expectation);
/// `t` itself when it does not have the key.
pub(super) fn remove<K: Keyed + Borrow<Q>, Q: Ord + ?Sized, V: Clone>(
    t: &Tree<K, V>,
    key: &Q,
) -> Tree<K, V> {
    let mut path = Vec::new();
    let mut cur = t.as_ref();
    while let Some(n) = cur {
        match key.cmp(n.key.borrow()) {
            Ordering::Equal => return up(path, join(n.left.clone(), n.right.clone())),
            Ordering::Less => {
                path.push((n, true));
                cur = n.left.as_ref();
            }
            Ordering::Greater => {
                path.push((n, false));
                cur = n.right.as_ref();
            }
        }
    }
    t.clone()
}

#[cfg(test)]
mod tests;
