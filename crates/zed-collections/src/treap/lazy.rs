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
//! the map cleared ([`Lazy::clear`]), and the child each keeps whole is made again under the
//! map, its root's item mapped ([`mapped`]), `O(1)` a node. So a walk makes at most two nodes a
//! level and is `O(depth)`, the depth of the plain treap of the same keys and priorities: the
//! maps change items but not keys' order, priorities or the shape, and the results are the trees
//! [`super::split`] and [`super::join`] give for the current items, node for node, the maps
//! cleared on the paths walked. This is the shape of the `join_under` zedc-preimage had before
//! its treap of pieces moved here (FAIL-s22-five-range-live-bytes), where pushing the map down to
//! both children before going on made a third of the nodes on a tagged path only to drop them.
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

use super::{DEEP, Item, Node, Tree, node};

/// How a walk reads the maps the items hold.
pub trait Lazy<I: Item> {
    /// Whether `item` holds a map other than the identity.
    fn pending(&self, item: &I) -> bool;
    /// The item `child` under the map `parent` holds: its fields mapped, and the map it holds
    /// the composite of its own and then `parent`'s.
    fn under(&self, parent: &I, child: &I) -> I;
    /// Makes `item` hold the identity map, its other fields kept. It changes the item in place,
    /// so that a walk, which owns the current item of each node it rebuilds, clears it with no
    /// copy: an item made again by value (`I { map: identity, ..item }`) was a move of the whole
    /// item, a call of `memcpy` for zedc-preimage's pieces (callgrind, s22
    /// `chain_five_range_live_scales`, 2026-11-28).
    fn clear(&self, item: &mut I);
    /// The summary of a subtree of summary `sum` under the map `parent` holds, when it can be
    /// made from `sum` alone in `O(1)`; `None`, the default, has the walk make it from the
    /// mapped item and the children's summaries ([`Item::sum`]), which reads the children and,
    /// for an item whose summary depends on its map, applies that map to each of them. A
    /// summary given here may differ from the one `Item::sum` would make (zedc-preimage's
    /// bounds on the values, which hold the values and may be wider); the walks keep the one
    /// they are given ([`mapped_as`]).
    #[inline]
    fn sum_under(&self, parent: &I, sum: &I::Sum) -> Option<I::Sum> {
        let _ = (parent, sum);
        None
    }
}

/// The tree of the one item `item`, of priority [`Item::priority`].
#[inline]
pub fn single<I: Item>(item: I) -> Tree<I> {
    let prio = item.priority();
    Some(node(item, prio, None, None))
}

/// The node of `item` and priority `prio` over `left` and `right`, its size and summary made
/// from theirs: for walks of a caller's own that rebuild a node over new children with the
/// priority it had (zedc-preimage's treap of pieces, whose splits return a piece cut in two).
/// The caller keeps the order and the heap: every key of `left` before `item`'s, every key of
/// `right` after, and no child's priority above `prio`.
#[inline]
pub fn node_at<I: Item>(item: I, prio: u64, left: Tree<I>, right: Tree<I>) -> Arc<Node<I>> {
    node(item, prio, left, right)
}

/// The tree of `n` with its root's item `item`, of the same key, children and priority: `O(1)`.
/// A whole tree moved by a map is its root's item under that map, made this way.
#[inline]
pub fn mapped<I: Item>(n: &Node<I>, item: I) -> Arc<Node<I>> {
    node(item, n.prio, n.left.clone(), n.right.clone())
}

/// [`mapped`] with the summary `sum` given rather than made from `item` and the children:
/// `O(1)` with no call of [`Item::sum`], for a caller that has the summary of the mapped subtree
/// from `n`'s ([`Lazy::sum_under`]). The caller keeps `sum` a summary of the subtree under the
/// map.
#[inline]
pub fn mapped_as<I: Item>(n: &Node<I>, item: I, sum: I::Sum) -> Arc<Node<I>> {
    Arc::new(Node {
        item,
        prio: n.prio,
        len: n.len,
        sum,
        left: n.left.clone(),
        right: n.right.clone(),
    })
}

/// The subtree `c`, of current item `item`, made again under the map its parent's current item
/// `parent` holds: its summary by [`Lazy::sum_under`] when that gives one, and otherwise made
/// from `item` and the children ([`mapped`]).
#[inline]
fn made_under<I: Item, L: Lazy<I>>(lazy: &L, parent: &I, c: &Node<I>, item: I) -> Arc<Node<I>> {
    match lazy.sum_under(parent, &c.sum) {
        Some(sum) => mapped_as(c, item, sum),
        None => mapped(c, item),
    }
}

/// The child `c` of a node whose current item `parent` holds a map, made again under it.
#[inline]
fn pushed<I: Item, L: Lazy<I>>(lazy: &L, parent: &I, c: &Tree<I>) -> Tree<I> {
    (c.as_deref()).map(|c| made_under(lazy, parent, c, lazy.under(parent, &c.item)))
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
        let mut item: I = item.unwrap_or_else(|| n.item.clone());
        let below = item.key().borrow() < key;
        let (keep, walk) = match below {
            true => (&n.left, &n.right),
            false => (&n.right, &n.left),
        };
        let (keep, item) = match lazy.pending(&item) {
            true => {
                cur = (walk.as_deref()).map(|c| (c, Some(lazy.under(&item, &c.item))));
                let keep = pushed(lazy, &item, keep);
                lazy.clear(&mut item);
                (keep, item)
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
///
/// It recurses, one call a node of the spine, as zedc-preimage's `join_under` did, and at
/// [`DEEP`] calls hands the two trees it has reached to `join_loop`, which keeps the rest of
/// the spine in a vector, so a chain of calls is at most `DEEP` frames deep for every tree, as
/// for the in-place walks of [`super`]. Complexity tradeoff: the whole spine kept in a vector
/// (one entry an item, its priority, a kept child and a flag) grew it by doubling once or more
/// a join, and the s22 chain families of zedc-preimage, whose items are five big numbers, did
/// up to 9.6% more instructions and 26% more bytes than with the recursive `join_under` (local
/// runs, 2026-11-27; the same cost [`DEEP`]'s comment in [`super`] measured for the paths of
/// the in-place walks). Each step keeps the current items it makes in its own frame and passes
/// the two trees down by reference (`Side`, three words), so an item is moved once a node of
/// the spine: passing them down by value, each with its root's current item, moved each item
/// two or more times a level, and callgrind put +148M instructions of `memcpy` on those moves
/// in `l01_25_preimage_catalog::bench::s22::chain_five_range_live_scales` (3,277M before the
/// treap of pieces moved here, 3,503M after; hm1, 2026-11-27). Tested by
/// `treap::tests::lazy_trees_agree_with_shifted_lists`, and the loop by
/// `treap::tests::a_lazy_join_of_two_paths_past_deep_calls`.
#[inline]
pub fn join<I: Item, L: Lazy<I>>(a: Tree<I>, b: Tree<I>, lazy: &L) -> Tree<I> {
    match (a, b) {
        (None, t) | (t, None) => t,
        (Some(x), Some(y)) => join_rec(Some(Side::stored(&x)), Some(Side::stored(&y)), lazy, 0),
    }
}

/// Where the current item of the root of a tree passed down by [`join`] is held.
enum Cur<'a, I: Item> {
    /// Nowhere: the stored item is current, as at the top and below an item holding no map.
    Stored,
    /// In a frame of [`join_rec`]: the slot that holds it until it is taken ([`Side::take`],
    /// [`Side::made`]), and the current item, in the same frame, whose map it lies under.
    Frame(&'a mut Option<I>, &'a I),
    /// At this place of [`join_loop`]'s spine: in [`Spined::walk`], under the map of
    /// [`Spined::item`].
    Spine(usize),
}

/// A tree passed down by [`join`]: its root and where the root's current item is held.
struct Side<'a, I: Item> {
    n: &'a Arc<Node<I>>,
    cur: Cur<'a, I>,
}

/// The message of a current item taken twice, which [`join`] never does: a tree passed down is
/// either kept by a step, which takes its root's item once, or is the bottom.
const HELD: &str = "the current item of a tree passed down is taken once";

impl<'a, I: Item> Side<'a, I> {
    #[inline]
    fn stored(n: &'a Arc<Node<I>>) -> Self {
        Side {
            n,
            cur: Cur::Stored,
        }
    }

    /// The root's current item; `spine` is [`join_loop`]'s.
    #[inline]
    fn item<'s>(&'s self, spine: &'s [Spined<I>]) -> &'s I {
        match &self.cur {
            Cur::Stored => &self.n.item,
            Cur::Frame(slot, _) => slot.as_ref().expect(HELD),
            Cur::Spine(at) => spine[*at].walk.as_ref().expect(HELD),
        }
    }

    /// The root's current item, taken from where it is held, for the step that keeps the root.
    #[inline]
    fn take(self, spine: &mut [Spined<I>]) -> I {
        match self.cur {
            Cur::Stored => self.n.item.clone(),
            Cur::Frame(slot, _) => slot.take().expect(HELD),
            Cur::Spine(at) => spine[at].walk.take().expect(HELD),
        }
    }

    /// The tree this stands for, made again under the map above it when it lies under one: the
    /// bottom of the spine.
    #[inline]
    fn made<L: Lazy<I>>(self, lazy: &L, spine: &mut [Spined<I>]) -> Arc<Node<I>> {
        match self.cur {
            Cur::Stored => self.n.clone(),
            Cur::Frame(slot, p) => made_under(lazy, p, self.n, slot.take().expect(HELD)),
            Cur::Spine(at) => {
                let Spined { item, walk, .. } = &mut spine[at];
                made_under(lazy, item, self.n, walk.take().expect(HELD))
            }
        }
    }
}

/// Whether the root of `x` comes before the root of `y` in [`join`]: the higher priority, ties
/// broken by the key.
#[inline]
fn first<I: Item>(x: &Side<'_, I>, y: &Side<'_, I>, spine: &[Spined<I>]) -> bool {
    (x.n.prio, x.item(spine).key()) > (y.n.prio, y.item(spine).key())
}

/// For the root `n`, of current item `item`, that a step of [`join`] keeps, the merge going on
/// into its left child when `left`: the child it keeps whole, made again under its map
/// ([`pushed`]); the child the merge goes on into; and that child's current item when `item`
/// holds a map.
#[inline]
fn kept<'n, I: Item, L: Lazy<I>>(
    lazy: &L,
    n: &'n Node<I>,
    item: &I,
    left: bool,
) -> (Tree<I>, &'n Tree<I>, Option<I>) {
    let (keep, walk) = match left {
        true => (&n.right, &n.left),
        false => (&n.left, &n.right),
    };
    match lazy.pending(item) {
        true => {
            let cur = walk.as_deref().map(|c| lazy.under(item, &c.item));
            (pushed(lazy, item, keep), walk, cur)
        }
        false => (keep.clone(), walk, None),
    }
}

/// Clears the map of `item`, if it holds one.
#[inline]
fn clear<I: Item, L: Lazy<I>>(lazy: &L, item: &mut I) {
    if lazy.pending(item) {
        lazy.clear(item);
    }
}

/// [`join`] of two sides, `depth` calls below the first. The frame holds the current item of
/// the root it keeps, its map not yet cleared, so that the subtree left at the bottom, which
/// lies under it, is made under it as the kept child is ([`made_under`]); and the current item
/// of the child the merge goes on into, which the call below takes.
fn join_rec<I: Item, L: Lazy<I>>(
    a: Option<Side<'_, I>>,
    b: Option<Side<'_, I>>,
    lazy: &L,
    depth: usize,
) -> Tree<I> {
    let (x, y) = match (a, b) {
        (None, s) | (s, None) => return s.map(|s| s.made(lazy, &mut [])),
        (Some(x), Some(y)) => (x, y),
    };
    if depth >= DEEP {
        return join_loop(x, y, lazy);
    }
    let left = !first(&x, &y, &[]);
    let (top, other) = match left {
        true => (y, x),
        false => (x, y),
    };
    let n = top.n;
    let mut item = top.take(&mut []);
    let (keep, walk, mut cur) = kept(lazy, n, &item, left);
    let held = cur.is_some();
    let walk = match walk {
        None => None,
        Some(c) => Some(Side {
            n: c,
            cur: match held {
                true => Cur::Frame(&mut cur, &item),
                false => Cur::Stored,
            },
        }),
    };
    let below = match left {
        true => join_rec(Some(other), walk, lazy, depth + 1),
        false => join_rec(walk, Some(other), lazy, depth + 1),
    };
    clear(lazy, &mut item);
    Some(match left {
        true => node(item, n.prio, below, keep),
        false => node(item, n.prio, keep, below),
    })
}

/// A node of [`join_loop`]'s spine.
struct Spined<I: Item> {
    /// Its current item, its map not yet cleared, as in [`join_rec`]'s frame.
    item: I,
    prio: u64,
    /// The child it keeps whole, made again under its map.
    keep: Tree<I>,
    /// Whether the merge went on into its left child.
    left: bool,
    /// The current item of the child the merge went on into when `item` holds a map, until the
    /// step below takes it.
    walk: Option<I>,
}

/// [`join_rec`] by a loop: the spine walked down and kept in a vector, then made up from its
/// bottom; node for node the same tree.
fn join_loop<'a, I: Item, L: Lazy<I>>(x: Side<'a, I>, y: Side<'a, I>, lazy: &L) -> Tree<I> {
    let mut spine: Vec<Spined<I>> = Vec::new();
    let (mut a, mut b) = (Some(x), Some(y));
    let mut bottom = loop {
        let (x, y) = match (a, b) {
            (None, s) | (s, None) => break s.map(|s| s.made(lazy, &mut spine)),
            (Some(x), Some(y)) => (x, y),
        };
        let left = !first(&x, &y, &spine);
        let (top, other) = match left {
            true => (y, x),
            false => (x, y),
        };
        let n = top.n;
        let item = top.take(&mut spine);
        let (keep, walk, cur) = kept(lazy, n, &item, left);
        let at = spine.len();
        let walk = walk.as_ref().map(|c| Side {
            n: c,
            cur: match cur.is_some() {
                true => Cur::Spine(at),
                false => Cur::Stored,
            },
        });
        (a, b) = match left {
            true => (Some(other), walk),
            false => (walk, Some(other)),
        };
        let prio = n.prio;
        spine.push(Spined {
            item,
            prio,
            keep,
            left,
            walk: cur,
        });
    };
    for s in spine.into_iter().rev() {
        let mut item = s.item;
        clear(lazy, &mut item);
        bottom = Some(match s.left {
            true => node(item, s.prio, bottom, s.keep),
            false => node(item, s.prio, s.keep, bottom),
        });
    }
    bottom
}
