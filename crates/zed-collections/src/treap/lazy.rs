//! Split and join of a treap whose items hold maps still to apply to the items below them (lazy
//! tags), so that a map applied to a whole tree costs `O(1)`: it is put at the root ([`mapped`])
//! and pushed down a level at a time by the walks that pass through a node. The map is part of
//! the item; a [`Lazy`], passed by argument, says how to read it.
//!
//! The item of a root is current: its key and fields are those of the tree it stands for. The map
//! an item holds is pending for the items below it, so the current item of a child is its stored
//! item under the maps of its ancestors, [`Lazy::under`] of its parent's current item. A walk
//! carries each node it goes on into with its current item, made from the parent's and the
//! stored one, and makes no node for it; the nodes it makes again hold their current items with
//! the map cleared ([`Lazy::cleared`]), and the child each keeps whole is made again under the
//! map, its root's item mapped ([`mapped`]), `O(1)` a node. So a walk makes at most two nodes a
//! level and is `O(depth)`, the depth of the plain treap of the same keys and priorities: the
//! maps change items but not keys' order, priorities or the shape, and the results are the trees
//! [`super::split`] and [`super::join`] give for the current items, node for node, the maps
//! cleared on the paths walked. This is the shape of zedc-preimage's `join_under`
//! (FAIL-s22-five-range-live-bytes), where pushing the map down to both children before going on
//! made a third of the nodes on a tagged path only to drop them.
//!
//! A summary ([`Item::sum`]) is made from the item and its children's summaries as stored, which
//! are of their subtrees before the item's map is applied to them: an item whose summary depends
//! on the map applies it in its `sum`. A node's priority is its item's [`Item::priority`], read
//! once, by [`single`]. The walks here compare priorities, ties broken by the key, and never ask
//! that a priority be a function of the key; [`super::insert`] and [`super::remove`] do, and an
//! item whose priority is not must not use them. The other functions of [`super`] read the
//! stored items and do not apply the maps.
//!
//! Tested by `treap::tests::lazy_trees_agree_with_shifted_lists`.

use std::borrow::Borrow;
use std::sync::Arc;

use super::{Item, Node, Tree, node};

/// How a walk reads the maps the items hold.
pub trait Lazy<I: Item> {
    /// Whether `item` holds a map other than the identity.
    fn pending(&self, item: &I) -> bool;
    /// The item `child` under the map `parent` holds: its fields mapped, and the map it holds
    /// the composite of its own and then `parent`'s.
    fn under(&self, parent: &I, child: &I) -> I;
    /// `item` holding the identity map, its fields kept.
    fn cleared(&self, item: &I) -> I;
}

/// The tree of the one item `item`, of priority [`Item::priority`].
#[inline]
pub fn single<I: Item>(item: I) -> Tree<I> {
    let prio = item.priority();
    Some(node(item, prio, None, None))
}

/// The tree of `n` with its root's item `item`, of the same key, children and priority: `O(1)`.
/// A whole tree moved by a map is its root's item under that map, made this way.
#[inline]
pub fn mapped<I: Item>(n: &Node<I>, item: I) -> Arc<Node<I>> {
    node(item, n.prio, n.left.clone(), n.right.clone())
}

/// The child `c` of a node whose current item `parent` holds a map, made again under it.
#[inline]
fn pushed<I: Item, L: Lazy<I>>(lazy: &L, parent: &I, c: &Tree<I>) -> Tree<I> {
    (c.as_deref()).map(|c| mapped(c, lazy.under(parent, &c.item)))
}

/// The items of `t` whose keys are below `key`, and the others: one walk down, `O(depth)`.
#[inline]
pub fn split_below<I, Q, L>(t: &Tree<I>, key: &Q, lazy: &L) -> (Tree<I>, Tree<I>)
where
    I: Item,
    I::Key: Borrow<Q>,
    Q: Ord + ?Sized,
    L: Lazy<I>,
{
    // Each node passed: its current item, cleared, its priority and the child it keeps.
    let (mut lefts, mut rights) = (Vec::new(), Vec::new());
    // The node the walk is at and its current item, `None` when it is the stored one.
    let mut cur = t.as_deref().map(|n| (n, None));
    while let Some((n, item)) = cur {
        let item: I = item.unwrap_or_else(|| n.item.clone());
        let below = item.key().borrow() < key;
        let (keep, walk) = match below {
            true => (&n.left, &n.right),
            false => (&n.right, &n.left),
        };
        let (keep, item) = match lazy.pending(&item) {
            true => {
                cur = (walk.as_deref()).map(|c| (c, Some(lazy.under(&item, &c.item))));
                (pushed(lazy, &item, keep), lazy.cleared(&item))
            }
            false => {
                cur = walk.as_deref().map(|c| (c, None));
                (keep.clone(), item)
            }
        };
        match below {
            true => lefts.push((item, n.prio, keep)),
            false => rights.push((item, n.prio, keep)),
        }
    }
    let mut l = None;
    for (item, prio, left) in lefts.into_iter().rev() {
        l = Some(node(item, prio, left, l));
    }
    let mut r = None;
    for (item, prio, right) in rights.into_iter().rev() {
        r = Some(node(item, prio, r, right));
    }
    (l, r)
}

/// The items of `a` and of `b`, every key of `a` before every key of `b`: the two merged down
/// one spine, the higher root first, `O(depth)`.
#[inline]
pub fn join<I: Item, L: Lazy<I>>(a: Tree<I>, b: Tree<I>, lazy: &L) -> Tree<I> {
    // Each node of the spine: its current item, cleared, its priority, the child it keeps, and
    // whether the merge went on into its left child.
    let mut spine: Vec<(I, u64, Tree<I>, bool)> = Vec::new();
    // The two trees and their roots' current items, `None` when they are the stored ones.
    let (mut a, mut b) = (a.map(|n| (n, None)), b.map(|n| (n, None)));
    let mut bottom = loop {
        match (a, b) {
            (None, x) | (x, None) => {
                break x.map(|(n, item)| match item {
                    Some(item) => mapped(&n, item),
                    None => n,
                });
            }
            (Some((x, ix)), Some((y, iy))) => {
                let x_above = {
                    let kx = ix.as_ref().unwrap_or(&x.item).key();
                    let ky = iy.as_ref().unwrap_or(&y.item).key();
                    (x.prio, kx) > (y.prio, ky)
                };
                // The root that stays, its current item, and the other tree.
                let (n, item, other) = match x_above {
                    true => (x, ix, (y, iy)),
                    false => (y, iy, (x, ix)),
                };
                let item = item.unwrap_or_else(|| n.item.clone());
                let (keep, walk) = match x_above {
                    true => (&n.left, &n.right),
                    false => (&n.right, &n.left),
                };
                let (keep, next, item) = match lazy.pending(&item) {
                    true => {
                        let next = walk.as_deref().map(|c| lazy.under(&item, &c.item));
                        (pushed(lazy, &item, keep), next, lazy.cleared(&item))
                    }
                    false => (keep.clone(), None, item),
                };
                let next = walk.clone().map(|c| (c, next));
                match x_above {
                    true => (a, b) = (next, Some(other)),
                    false => (a, b) = (Some(other), next),
                }
                spine.push((item, n.prio, keep, !x_above));
            }
        }
    };
    for (item, prio, keep, left) in spine.into_iter().rev() {
        bottom = Some(match left {
            true => node(item, prio, bottom, keep),
            false => node(item, prio, keep, bottom),
        });
    }
    bottom
}
