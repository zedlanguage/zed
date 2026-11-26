//! Persistent treaps with sizes and a summary of each subtree, built from two operations,
//! `split` and `join`: get, split, join, insertion, removal, the place of a key and the key at a
//! place, each `O(log n)` expected (plan row DRY-persistent-trees-2026-11-26, which takes the
//! split and join copies of the workspace onto this one). An item says its key, its priority and
//! how its subtree's summary is made from its children's ([`Item`]).
//!
//! Source, for this module and the join-based set operations of zed-kernel's `bdd::set` and
//! `bdd::settings`. G. E. Blelloch, D. Ferizovic and Y. Sun, "Just join for parallel ordered
//! sets", SPAA 2016, 253-264, doi:10.1145/2935764.2935768; full version arXiv:1602.02120
//! (November 2016, titled "Parallel ordered sets using join"), whose numbering is used here.
//! Section 3, Figure 5, the treap JOIN(TL, k, TR): it "first picks the key with the highest
//! priority among k, k(TL) and k(TR) as the root" and recurses on the side whose root was not
//! taken; Lemma 4 and Theorem 1: O(log t) expected work "if k has the t-th highest priority among
//! all keys". Section 4: SPLIT(T, k), Theorem 2: O(log |T|) w.h.p. for treaps; JOIN2(TL, TR), two
//! trees with no key between, Theorem 3: O(r(TL) + r(TR)); UNION, INTERSECT and DIFFERENCE split
//! one tree at the other's root, recurse on the two sides and join the results; Theorem 4 (the
//! main theorem): their work on trees of sizes `m <= n` is `O(m log(n/m + 1))` in expectation for
//! treaps. In this module: `join` is JOIN2, merging the facing spines of the two trees, higher
//! priority first, which is JOIN's recursion with no middle key; `split` is one walk down the
//! search path that hands each node to the left or right result, the standard treap split
//! (Seidel and Aragon 1996, doi:10.1007/BF01940876; the full comment is in module
//! [`crate::priority`], at the head of `priority.rs`) rather than the paper's split by JOIN, with
//! the same result, since a treap's shape is fixed by its keys and priorities. Departures: the
//! paper's priorities are independent and uniform; here they are the 8-wise or 5-wise
//! independent draw of module [`crate::priority`], under which the bounds used are proved there.
//! The size and the summary kept at each node are the augmentation of Y. Sun, D. Ferizovic and
//! G. E. Blelloch, "PAM: parallel augmented maps", PPoPP 2018, 290-304,
//! doi:10.1145/3178487.3178509. Checked 2026-11-19 against the full version's text (sections
//! 2-5) and Crossref for both; the SPAA text was not read. PAM read 2026-11-20, PDF, Sci-Hub,
//! verification only; section 4, "Augmentation": "storing with every tree node the augmented sum
//! of the subtree rooted at that node ... when creating a node with a left child L, right child
//! R, key k and value v the augmented value can be calculated as f(A(L), f(g(k, v), A(R)))", and
//! "creation of new nodes is handled in JOIN"; here the size is the sum with `g` 1 and `f` `+`,
//! and [`Item::sum`] is `f` and `g` of the item's own summary. The paper lists treaps among the
//! trees PAM implements. Tested by `treap::tests`: the treap against a `BTreeMap` under random
//! operations (wrong keys, values, sizes, summaries or heap order), one shape for one set of
//! keys; no test measures the work.
//!
//! A tree is shared, never changed: an operation makes new nodes along the paths it changes and
//! shares every subtree it leaves alone. A node's priority is a function of its key drawn at
//! random once per run ([`Item::priority`], module [`crate::priority`]), ties broken by the order
//! of the keys, so in a run the keys of a tree fix its shape whatever order they came in. Seidel
//! and Aragon's bound on the expected depth, `O(log n)` for every set of keys, holds for keys at
//! distinct points of the draw (module [`crate::priority`]).
//!
//! Every walk keeps a stack of its own, and a tree is dropped in a loop, so the stack needed does
//! not depend on a tree's height.

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::sync::Arc;

/// An item of a treap: its key, its priority, and the summary of a subtree it is the root of.
pub trait Item: Clone {
    /// The order of the items.
    type Key: Ord;
    /// What each node keeps of its subtree beside the size; `()` for none.
    type Sum;
    /// The item's key.
    fn key(&self) -> &Self::Key;
    /// The item's priority: a random function of the key, one per use of the treap, drawn once
    /// per run (module [`crate::priority`]). Read once, when the item's node is first made.
    fn priority(&self) -> u64;
    /// The summary of a subtree with this item at its root over children of summaries `left`
    /// and `right` (`None`: no child).
    fn sum(&self, left: Option<&Self::Sum>, right: Option<&Self::Sum>) -> Self::Sum;
}

/// A node: its item and priority, the number of items and the summary of its subtree, and the
/// trees of the items before and after it.
pub struct Node<I: Item> {
    item: I,
    prio: u64,
    len: usize,
    sum: I::Sum,
    left: Tree<I>,
    right: Tree<I>,
}

/// A tree: its root, or `None` when empty.
pub type Tree<I> = Option<Arc<Node<I>>>;

/// What [`split`] returns: the items before the key, the key's node if the tree has one, and
/// the items after it.
pub type Split<'a, I> = (Tree<I>, Option<&'a Arc<Node<I>>>, Tree<I>);

/// A tree is freed in a loop, a node whose last handle goes handing its children on, so a tree
/// of any height is dropped on a small stack.
impl<I: Item> Drop for Node<I> {
    fn drop(&mut self) {
        // Only children whose last handle this is are walked; the stack allocates nothing
        // until one is, and a node popped from it has no children left when it drops.
        let mut stack: Vec<Node<I>> = Vec::new();
        let free = |c: Tree<I>, stack: &mut Vec<Node<I>>| {
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

// Every function of this module is `#[inline]`. The release profile builds a crate as 16 codegen
// units, with no inlining across them but local ThinLTO's of small functions, and a generic
// function of another crate is made in a unit of its own, away from its callers; `#[inline]` makes
// a copy in each unit that calls it. Instructions of "a list built a literal at a time"
// (zed-kernel `types::bdd::bench`) at 2048 / 16384 literals, v5e1 2026-11-26 (dry-coll): the
// private treap of the decision-list index this module replaced, 2,191,552,957 / 20,773,857,615;
// this module without `#[inline]`, 2,239,024,408 / 21,254,958,830 (2.2% and 2.3% more); with it,
// 2,213,753,603 / 21,000,005,054 (1.0% and 1.1% more). The cause was not profiled; the drop is
// what a lost inlining across units predicts.

/// Whether node `a` stands above node `b`: the higher priority, ties broken by the key.
#[inline]
fn above<I: Item>(a: &Node<I>, b: &Node<I>) -> bool {
    (a.prio, a.item.key()) > (b.prio, b.item.key())
}

/// The node of `item` and priority `prio` over `left` and `right`, its size and summary made
/// from theirs.
#[inline]
fn node<I: Item>(item: I, prio: u64, left: Tree<I>, right: Tree<I>) -> Arc<Node<I>> {
    Arc::new(Node {
        len: 1 + len(&left) + len(&right),
        sum: item.sum(
            left.as_deref().map(|n| &n.sum),
            right.as_deref().map(|n| &n.sum),
        ),
        item,
        prio,
        left,
        right,
    })
}

/// The node `n` made again over `left` and `right`, its priority kept rather than computed.
#[inline]
fn again<I: Item>(n: &Node<I>, left: Tree<I>, right: Tree<I>) -> Arc<Node<I>> {
    node(n.item.clone(), n.prio, left, right)
}

/// The path `path` from the root down, each node with the side taken from it, made again over
/// `bottom`, the new subtree where the path ends.
#[inline]
fn up<I: Item>(path: Vec<(&Arc<Node<I>>, bool)>, mut bottom: Tree<I>) -> Tree<I> {
    for (n, left) in path.into_iter().rev() {
        bottom = Some(match left {
            true => again(n, bottom, n.right.clone()),
            false => again(n, n.left.clone(), bottom),
        });
    }
    bottom
}

/// The number of items.
#[inline]
pub fn len<I: Item>(t: &Tree<I>) -> usize {
    t.as_ref().map_or(0, |n| n.len)
}

/// The item of `key`, if the tree has it: one walk down, `O(log n)`.
#[inline]
pub fn get<'a, I: Item, Q: Ord + ?Sized>(t: &'a Tree<I>, key: &Q) -> Option<&'a I>
where
    I::Key: Borrow<Q>,
{
    let mut cur = t.as_deref();
    while let Some(n) = cur {
        cur = match key.cmp(n.item.key().borrow()) {
            Ordering::Less => n.left.as_deref(),
            Ordering::Greater => n.right.as_deref(),
            Ordering::Equal => return Some(&n.item),
        };
    }
    None
}

/// The place of `key` in order (from 0), if the tree has it: one walk down, the sizes of the
/// left subtrees passed to the right added, `O(log n)`.
#[inline]
pub fn place<I: Item, Q: Ord + ?Sized>(t: &Tree<I>, key: &Q) -> Option<usize>
where
    I::Key: Borrow<Q>,
{
    let (mut cur, mut below) = (t.as_deref(), 0);
    while let Some(n) = cur {
        match key.cmp(n.item.key().borrow()) {
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

/// The item at place `k` (from 0) in order; the tree has more than `k` items.
#[inline]
pub fn nth<I: Item>(t: &Tree<I>, mut k: usize) -> &I {
    let mut at = t.as_deref().expect("the tree has the place asked for");
    loop {
        let ln = len(&at.left);
        match k.cmp(&ln) {
            Ordering::Less => at = at.left.as_deref().expect("the place is on the left"),
            Ordering::Equal => return &at.item,
            Ordering::Greater => {
                k -= ln + 1;
                at = at.right.as_deref().expect("the place is on the right");
            }
        }
    }
}

/// The items in order, by one walk with a stack of its own.
#[inline]
pub fn iter<I: Item>(t: &Tree<I>) -> impl Iterator<Item = &I> {
    let (mut stack, mut at) = (Vec::new(), t.as_deref());
    std::iter::from_fn(move || {
        while let Some(n) = at {
            stack.push(n);
            at = n.left.as_deref();
        }
        let n = stack.pop()?;
        at = n.right.as_deref();
        Some(&n.item)
    })
}

/// The items of `t` before `key`, the node of `key` if `t` has one, and the items after it: one
/// walk down from the root, the nodes passed made again on each side, `O(height)`.
#[inline]
pub fn split<'a, I: Item, Q: Ord + ?Sized>(t: &'a Tree<I>, key: &Q) -> Split<'a, I>
where
    I::Key: Borrow<Q>,
{
    let (mut lefts, mut rights) = (Vec::new(), Vec::new());
    let mut cur = t.as_ref();
    let (mut l, mut r, mut found) = (None, None, None);
    while let Some(n) = cur {
        match n.item.key().borrow().cmp(key) {
            Ordering::Less => {
                lefts.push(n);
                cur = n.right.as_ref();
            }
            Ordering::Greater => {
                rights.push(n);
                cur = n.left.as_ref();
            }
            Ordering::Equal => {
                (l, r, found) = (n.left.clone(), n.right.clone(), Some(n));
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
    (l, found, r)
}

/// The first `k` items of `t`: one walk down by the sizes, the nodes passed on the left made
/// again, `O(height)`. A cut at either end leaves `t` whole or empty.
#[inline]
pub fn prefix<I: Item>(t: &Tree<I>, k: usize) -> Tree<I> {
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

/// The items of `a` and of `b`, every key of `a` before every key of `b`: the two merged down
/// one spine, the higher root first, `O(height)`.
#[inline]
pub fn join<I: Item>(a: Tree<I>, b: Tree<I>) -> Tree<I> {
    let mut spine: Vec<(Arc<Node<I>>, bool)> = Vec::new();
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

/// `t` with `item` in place of the item of its key, or added: one walk down while the nodes
/// stand above the new one, then the subtree there split at the key (or the key's own node given
/// the new item), the path made again, `O(log n)` expected.
///
/// Complexity tradeoff: an insertion by `split` and two `join`s (Blelloch, Ferizovic and Sun,
/// doi:10.1145/2935764.2935768) makes every node on the search path again and then the spines
/// it joins, about three times the nodes; this walk (Seidel and Aragon's insertion,
/// doi:10.1007/BF01940876, without rotations) makes the path above the new node and splits
/// only the subtree below it, whose two spines have `O(1)` nodes in expectation. The shape is
/// the same, since a treap's shape is fixed by its keys.
#[inline]
pub fn insert<I: Item>(t: &Tree<I>, item: I) -> Tree<I> {
    let prio = item.priority();
    let mut path = Vec::new();
    let mut cur = t.as_ref();
    // A node of the path stands above the new one: a node of the same key has its priority, so
    // the walk stops there, the key's node being below every node above the new one.
    while let Some(n) = cur
        && (n.prio, n.item.key()) > (prio, item.key())
    {
        let left = item.key() < n.item.key();
        path.push((n, left));
        cur = if left {
            n.left.as_ref()
        } else {
            n.right.as_ref()
        };
    }
    let bottom = match cur {
        Some(n) if n.item.key() == item.key() => node(item, prio, n.left.clone(), n.right.clone()),
        _ => {
            let sub = cur.cloned();
            let (l, found, r) = split(&sub, item.key());
            // The subtree split never holds the key. The key's own node, if the tree has it,
            // has the key's priority, and every node above it in the tree stands above it in the
            // order `(prio, key)`; so the walk above follows its ancestors down to it and stops
            // there, and gives it the new item without a split. Facts used: every node's `prio`
            // is its item's `priority()` (`insert` sets it, `again` keeps it), a function of the
            // key in a run (module [`crate::priority`]); the heap order by `above` holds in
            // every tree (`insert` puts the new node below the nodes above it, `split` and
            // `join` keep it); and the search path to a key in a search tree is its node's
            // ancestors, then the node. Test: `a_treap_agrees_with_an_ordered_map`
            // (`treap::tests`) inserts keys drawn from 300 at about half of 4000 steps, so most
            // keys are inserted again, and checks the heap order (`sound`) after each step; a
            // wrong proof would fail this check there. It cannot catch an item type whose
            // priority is not a function of the key.
            assert!(
                found.is_none(),
                "insert splits only a subtree without the key"
            );
            node(item, prio, l, r)
        }
    };
    up(path, Some(bottom))
}

/// `t` without `key`: one walk down to its node, whose two subtrees are joined in its place, the
/// path made again, `O(log n)` expected (the joined spines have `O(1)` nodes in expectation);
/// `t` itself when it does not have the key.
#[inline]
pub fn remove<I: Item, Q: Ord + ?Sized>(t: &Tree<I>, key: &Q) -> Tree<I>
where
    I::Key: Borrow<Q>,
{
    let mut path = Vec::new();
    let mut cur = t.as_ref();
    while let Some(n) = cur {
        match key.cmp(n.item.key().borrow()) {
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
