//! Persistent treaps with sizes and a summary of each subtree, built from two operations,
//! `split` and `join`: get, split, join, insertion, removal, the place of a key and the key at a
//! place, each `O(log n)` expected; a tree made from sorted items in `O(n)`; and the union and
//! meet of two trees (plan row DRY-persistent-trees-2026-11-26, which takes the
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
//! keys, the in-place operations against the persistent ones; no test measures the work.
//!
//! A tree is shared, never changed: an operation makes new nodes along the paths it changes and
//! shares every subtree it leaves alone. The in-place operations (`get_mut`, `insert_mut`,
//! `remove_mut`) give the same trees, changing the nodes a tree alone holds and copying those it
//! shares with another, which is left as it was. A node's priority is a function of its key drawn
//! at random once per run ([`Item::priority`], module [`crate::priority`]), ties broken by the
//! order of the keys, so in a run the keys of a tree fix its shape whatever order they came in.
//! Seidel and Aragon's bound on the expected depth, `O(log n)` for every set of keys, holds for
//! keys at distinct points of the draw (module [`crate::priority`]).
//!
//! The walks of the persistent operations keep stacks of their own; the in-place operations
//! recurse to [`DEEP`] calls and the drop of a tree to `DEEPEST` levels, each going on in a loop
//! past that, so the stack needed does not depend on a tree's height.
//!
//! Module [`lazy`] splits and joins trees whose items hold maps still to apply below them, a
//! lazy tag passed by argument, so that a whole tree moves by a map in `O(1)`.

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

// A tree is freed by the drop the compiler makes, which frees a node's children before the
// node, in place, with one count added: [`DROPPING`], the levels of `Node::drop` on this
// thread's stack. Below [`DEEPEST`] levels a node frees its children by the compiler's drop of
// their handles, a recursion; at `DEEPEST` it hands them to [`free_in_a_loop`], which frees the
// rest with a vector of handles. So the stack holds at most `DEEPEST` levels of the drop,
// whatever the tree's height (STACK-treap-drop-depth), and a tree in an item of a tree counts on
// from the levels of the tree it is in, so nesting does not add levels. A panic out of a drop
// leaves the count high, and later drops on that thread go to the loop sooner: slower, still
// right.
//
// Complexity tradeoff: freeing every node by `Arc::into_inner` moves the node out of its
// allocation before freeing it, and the hull benchmark "the join of hulls, a row among the
// others" (zedc-presburger `hull/rows.rs`, 16,384 joins of a hull of 16,384 rows, each freeing
// the path a change copied) took, under callgrind, 537,530,703 instructions with a `Drop` that
// freed every node in a loop that way (l41 and l42, 2026-11-26) and 556,824,893 to 566,141,379
// with a recursion of 51 levels on such moves (hm1, 2026-11-27, base aaceb2e10), against
// 522,673,364 with the drop the compiler makes (STACK-treap-drop-depth). The count moves
// nothing: it reads and writes a thread-local word twice for each node freed.

/// The levels of `Node::drop` on this thread's stack (comment above). A `#[thread_local]`
/// static, not `thread_local!`: the macro's `LocalKey` was reached through its accessor, three
/// calls a node freed that were not inlined (objdump, 3a821478d), and cost the hull joins
/// +5.99% to +7.56% in instructions; this static is read and written by one instruction each,
/// `%fs`-relative on x86_64 Linux (objdump of a probe built by the pinned nightly-2026-11-18,
/// 2026-11-27). It holds no value to drop, which the feature does not run.
#[thread_local]
static DROPPING: std::cell::Cell<u32> = std::cell::Cell::new(0);

/// The levels of `Node::drop` past which a node's children are freed by [`free_in_a_loop`].
///
/// L. Devroye, "A note on the height of binary search trees", J. ACM 33(3):489-498, 1986,
/// doi:10.1145/5925.5930, for the tree built "by standard insertions from a random permutation of
/// 1, ..., n" (abstract), Theorem 5.1 (p. 494): "Let c = 4.31107 ... be the unique solution of the
/// equation c log(2e/c) = 1, c ≥ 2. Then: A. H_n/log n → c in probability as n → ∞." The log is
/// natural (`4.31107 · ln(2e / 4.31107) = 1.000`). A treap's shape is that of the binary search
/// tree built by inserting its keys in order of falling priority, and priorities drawn
/// independently put the keys in that order as a random permutation, so a treap has the height of
/// that tree: about `4.31107 · ln 2^32 = 95.6` at `n = 2^32`, below 128. So a tree of keys of
/// random priorities is freed with no vector, and only a tall tree (keys tied at one point of the
/// draw, or chosen against it) reaches the loop. The theorem is a limit in probability, not a
/// bound; the stack is bounded by the loop whatever the height, and the test
/// `a_path_is_dropped_on_a_small_stack` drops paths of 100,000 nodes on 64 KiB.
const DEEPEST: u32 = 128;

impl<I: Item> Drop for Node<I> {
    #[inline]
    fn drop(&mut self) {
        let depth = DROPPING.get();
        if depth < DEEPEST {
            DROPPING.set(depth + 1);
            drop(self.left.take());
            drop(self.right.take());
            DROPPING.set(depth);
        } else if self.left.is_some() || self.right.is_some() {
            free_in_a_loop(self.left.take(), self.right.take());
        }
    }
}

/// Frees `left` and `right` with a vector of the handles still to free, a node at a time: the
/// nodes freed here run `Node::drop` at `DEEPEST` levels or more, with no children left.
#[cold]
#[inline(never)]
fn free_in_a_loop<I: Item>(left: Tree<I>, right: Tree<I>) {
    let mut stack: Vec<Arc<Node<I>>> = left.into_iter().chain(right).collect();
    while let Some(a) = stack.pop() {
        if let Some(mut n) = Arc::into_inner(a) {
            stack.extend(n.left.take());
            stack.extend(n.right.take());
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

/// The tree of `items`, whose keys are strictly increasing: its shape found as a Cartesian
/// tree by priority with one stack and each node made once over its children, `O(k)` (module
/// [`crate::cartesian`], which cites, quotes and proves the construction). The items go to
/// [`crate::cartesian::build`] themselves, ordered by their keys (`ByKey`), so its ties,
/// broken by the greater key, are broken as `above` breaks them.
// Complexity tradeoff: the first version handed `build` the indices `0..k` and kept the items in
// a vector of `Option`s taken one by one, two more vectors of `k` and a pass over each; the
// sets of settings of zed-kernel's `bdd` are built so many times (`settings::from_keys`) that
// the forced-atoms benches took 8.0 to 8.4% more instructions than with the private treap that
// passed its keys to `build` directly. `ByKey` is `repr(transparent)`, so the `map` and
// `collect` that wrap the items reuse their vector in place: one vector of `k` priorities is
// the only one made here, as before. Measured locally against origin/main fffd2df52
// (instructions at n and 8n): the three forced-atoms benches +2.54% to +2.62% with this, against
// +8.02% to +8.40% with the first version; `a_binding_over_many_inputs` -3.26% and -5.09% with
// either. The 2.6% left is not placed by a profile; inferred to be the generic treap's own work
// for the settings (its `Sum` and node layout) rather than this function's.
#[inline]
pub fn from_sorted<I: Item>(items: Vec<I>) -> Tree<I> {
    debug_assert!(
        items.windows(2).all(|w| w[0].key() < w[1].key()),
        "keys strictly increasing"
    );
    let prios: Vec<u64> = items.iter().map(Item::priority).collect();
    let items: Vec<ByKey<I>> = items.into_iter().map(ByKey).collect();
    crate::cartesian::build(items, &prios, |i, ByKey(item), l, r| {
        node(item, prios[i], l, r)
    })
}

/// An item ordered by its key alone, for [`from_sorted`].
#[repr(transparent)]
struct ByKey<I: Item>(I);

impl<I: Item> PartialEq for ByKey<I> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0.key() == other.0.key()
    }
}

impl<I: Item> Eq for ByKey<I> {}

impl<I: Item> PartialOrd for ByKey<I> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<I: Item> Ord for ByKey<I> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.key().cmp(other.0.key())
    }
}

/// Whether two trees are one node (or both empty); a shortcut only, never an order.
#[inline]
fn same<I: Item>(x: &Tree<I>, y: &Tree<I>) -> bool {
    match (x, y) {
        (Some(x), Some(y)) => Arc::ptr_eq(x, y),
        (None, None) => true,
        _ => false,
    }
}

/// The node `n` over `left` and `right`, `n` itself when they are its own children.
#[inline]
fn remake<I: Item>(n: &Arc<Node<I>>, left: Tree<I>, right: Tree<I>) -> Arc<Node<I>> {
    if same(&left, &n.left) && same(&right, &n.right) {
        return n.clone();
    }
    again(n, left, right)
}

/// The items of `x` and `y` whose key is in either (`union`) or in both (`meet`), a key in both
/// with the item of `y`: from the roots down, the higher root kept and the other tree split at
/// its key, the two sides combined past it, and for `meet` the root kept only when the other
/// tree had its key. Two subtrees that are one node are their own union and meet, and a node
/// over children left as they were is shared, not made again. For trees of sizes `m <= n`,
/// `O(m log(n/m + 1))` expected (Blelloch, Ferizovic and Sun, Theorem 4 of the full version,
/// cited at the head of this module; for the draw of module [`crate::priority`], the finger bound
/// proved there, plus the keys that share a point). A walk with stacks of its own.
///
/// Proof that a key in both keeps `y`'s item. A step combines subtrees `x'` and `y'`; say the
/// higher root's key `k` is in both. A node's rank is its priority and key, so `k`'s node has
/// one rank in both trees, and no node of `x'` or `y'` ranks above it, as it is the higher
/// root's rank. In a heap-ordered tree the node of the top rank is the root, so `k`'s node is
/// the root of both `x'` and `y'`; the two roots tie, [`above`] is false for them, and `y'`'s
/// root is kept, `x'`'s dropped by the split. The sides below keep `x`'s subtree first, so the
/// same holds at every step. A key in one tree only keeps its own item. Tested by
/// `treap::tests::union_and_meet_agree_with_ordered_maps`.
#[inline]
fn combine<I: Item>(x: &Tree<I>, y: &Tree<I>, keep_one_sided: bool) -> Tree<I> {
    /// A pair of subtrees to combine, or a node to make over the two combined last: with its
    /// item kept, or (for a meet whose other tree lacked its key) the two joined.
    enum Step<I: Item> {
        Combine(Tree<I>, Tree<I>),
        Make(Arc<Node<I>>, bool),
    }
    let mut todo = vec![Step::Combine(x.clone(), y.clone())];
    let mut done: Vec<Tree<I>> = Vec::new();
    while let Some(step) = todo.pop() {
        let (x, y) = match step {
            Step::Make(n, kept) => {
                let r = done.pop().expect("the right side is combined");
                let l = done.pop().expect("the left side is combined");
                done.push(if kept {
                    Some(remake(&n, l, r))
                } else {
                    join(l, r)
                });
                continue;
            }
            Step::Combine(None, t) | Step::Combine(t, None) => {
                done.push(if keep_one_sided { t } else { None });
                continue;
            }
            Step::Combine(Some(x), Some(y)) if Arc::ptr_eq(&x, &y) => {
                done.push(Some(x));
                continue;
            }
            Step::Combine(Some(x), Some(y)) => (x, y),
        };
        let (hi, lo, hi_is_x) = if above(&x, &y) {
            (x, y, true)
        } else {
            (y, x, false)
        };
        let lo = Some(lo);
        let (l, found, r) = split(&lo, hi.item.key());
        let kept = keep_one_sided || found.is_some();
        let (hl, hr) = (hi.left.clone(), hi.right.clone());
        todo.push(Step::Make(hi, kept));
        // The sides keep the trees' order, `x`'s first, so that ties below go to `y` as well.
        if hi_is_x {
            todo.push(Step::Combine(hr, r));
            todo.push(Step::Combine(hl, l));
        } else {
            todo.push(Step::Combine(r, hr));
            todo.push(Step::Combine(l, hl));
        }
    }
    done.pop().expect("the two trees are combined")
}

/// The items of `x` and `y`, a key in both with the item of `y` (`combine`).
#[inline]
pub fn union<I: Item>(x: &Tree<I>, y: &Tree<I>) -> Tree<I> {
    combine(x, y, true)
}

/// The items of `y` whose key is also in `x` (`combine`).
#[inline]
pub fn meet<I: Item>(x: &Tree<I>, y: &Tree<I>) -> Tree<I> {
    combine(x, y, false)
}

impl<I: Item> Node<I> {
    /// The node's item.
    #[inline]
    pub fn item(&self) -> &I {
        &self.item
    }

    /// The tree of the items before this one.
    #[inline]
    pub fn left(&self) -> &Tree<I> {
        &self.left
    }

    /// The tree of the items after this one.
    #[inline]
    pub fn right(&self) -> &Tree<I> {
        &self.right
    }

    /// The summary of the node's subtree.
    #[inline]
    pub fn sum(&self) -> &I::Sum {
        &self.sum
    }

    /// The node's place in the heap order, the higher above: its priority, ties broken by the
    /// key. Two trees of one set of keys have one shape in a run, so a walk of two trees side by
    /// side can open the higher of two roots first and meet the subtrees they share at one place.
    #[inline]
    pub fn rank(&self) -> (u64, &I::Key) {
        (self.prio, self.item.key())
    }
}

/// A copy of a node that another tree shares, made by the in-place operations before they change
/// it: its children stay shared with the original.
impl<I: Item> Clone for Node<I>
where
    I::Sum: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        Node {
            item: self.item.clone(),
            prio: self.prio,
            len: self.len,
            sum: self.sum.clone(),
            left: self.left.clone(),
            right: self.right.clone(),
        }
    }
}

// The in-place operations. Complexity tradeoff: the persistent `insert` and `remove` make every
// node on the paths they change again, an allocation each; these change in place the nodes that
// this tree alone holds and copy only those another tree shares (`Arc::make_mut`), so a tree
// changed many times between copies allocates near nothing but its new nodes. The walks, the
// shapes and the `O(log n)` expected bounds are those of `insert` and `remove`; the results are
// the same trees. They recurse only as deep as the tree: `insert_at` one call a node of the path
// to the new node's place and `split_mut` one a node of the path below it, so at most the depth
// of the tree in all; `remove_at` one a node of the path to the key, and `join_mut` one a node of
// the right spine of the key's left subtree and of the left spine of its right one, each at most
// the depth below the key, so at most twice the depth. The depth is `O(log n)` expected
// (`crate::priority`). Complexity tradeoff: kept in a vector instead, a path that grows as the
// walk goes down allocated four or five times an operation, and the hull benchmarks of
// zedc-presburger (`hull/rows.rs`) did 9% to 19% more instructions and 8% to 26% more bytes
// than with the recursive treap that file had before (v5e1, 2026-11-26); recursive, they did
// 0.25% to 1.0% more instructions (l42, 2026-11-26). Tested by
// `treap::tests::the_in_place_operations_give_the_persistent_trees`, which also checks that
// copies taken before a change are left as they were.
//
// The depth is only expected, not bounded: whenever the draw of priorities is known
// (`ZED_TREAP_SEED`, which every bench run sets to 0), keys chosen against it make a path, and
// a recursion one call a node of it overflows the stack (FAIL-treap-inplace-recursion-depth).
// So each recursion counts its calls, one count shared by `insert_at` and the `split_mut` it
// calls and by `remove_at` and its `join_mut`, and at [`DEEP`] calls hands the subtree it has
// reached to a loop ([`split_loop`], [`join_loop`], [`insert_loop`], [`remove_loop`]) that keeps
// the path in vectors on the heap. A chain of calls is then at most `DEEP` frames deep for
// every tree. The loops do what the recursions do, node for node: each takes the children out
// of the nodes it passes (made this tree's alone first, by `own`, as the recursions do),
// pushes the nodes on its vectors, and on the way back puts the new children in and refreshes
// the node; so the trees, and the copies another tree shares, are the same, and no node is
// freed but the one `remove` takes out, whose children are taken from it first. They do not
// fall back on the persistent `split` and `join`: those make the path again, and the old path,
// freed when the last handle to it goes, is freed by the compiler's drop, a recursion as deep
// as the path (STACK-treap-drop-depth). Tested by
// `treap::tests::the_in_place_operations_take_a_path_of_any_depth`, on paths of 100,000 and 200,000
// nodes in a thread of a 1 MiB stack.

/// The calls of one in-place recursion before it hands its subtree to a loop. Why 256: the
/// value changes only the cost, never a tree, since the loops do what the recursions do; the
/// loops are slower by the allocations of their vectors (the comment above measured that cost),
/// so the value is set where random trees do not reach. Module [`crate::priority`] proves a
/// node's expected depth `O(log n)`, at most `T0 + n(n - 1)/p + 2c H_n`, with no value for `c`;
/// for priorities drawn independently `c = 1` (the exact expected depth of a node of a random
/// binary search tree is below `2 H_n`, about `2 ln n`), 56 at `n = 2^40`, so 256 is more than
/// four times that (inferred for the 5-wise draw, whose `c` is not known). The stack it
/// allows, 256 frames of these small functions, is far under the 2 MiB of a thread; the test
/// above runs them in 1 MiB, unoptimized. The treaps of other crates that recurse to the same
/// depth use it too (zedc-preimage's `divisors::Sets::union`).
pub const DEEP: usize = 256;

/// The node `n` made this tree's alone, copied if another tree shares it, to change in place.
#[inline]
fn own<I: Item>(n: &mut Arc<Node<I>>) -> &mut Node<I>
where
    I::Sum: Clone,
{
    Arc::make_mut(n)
}

/// The size and summary of `n` made again from its item and children.
#[inline]
fn refresh<I: Item>(n: &mut Node<I>) {
    n.len = 1 + len(&n.left) + len(&n.right);
    n.sum = n.item.sum(
        n.left.as_deref().map(|c| &c.sum),
        n.right.as_deref().map(|c| &c.sum),
    );
}

/// The items of `t` before `key` and those after it, `t` holding no item of `key`: `split` in
/// place, `depth` calls below the walk's first.
#[inline]
fn split_mut<I: Item>(t: Tree<I>, key: &I::Key, depth: usize) -> (Tree<I>, Tree<I>)
where
    I::Sum: Clone,
{
    if depth >= DEEP {
        return split_loop(t, key);
    }
    let Some(mut n) = t else {
        return (None, None);
    };
    let m = own(&mut n);
    match m.item.key().cmp(key) {
        Ordering::Less => {
            let (below, above) = split_mut(m.right.take(), key, depth + 1);
            m.right = below;
            refresh(m);
            (Some(n), above)
        }
        Ordering::Greater => {
            let (below, above) = split_mut(m.left.take(), key, depth + 1);
            m.left = above;
            refresh(m);
            (below, Some(n))
        }
        Ordering::Equal => unreachable!("split_mut is given a tree without the key"),
    }
}

/// [`split_mut`] by a loop: the nodes below the key kept on one vector and those above on
/// another, root first, each with the child on the key's side taken out; then each side made
/// up from its bottom.
fn split_loop<I: Item>(t: Tree<I>, key: &I::Key) -> (Tree<I>, Tree<I>)
where
    I::Sum: Clone,
{
    let (mut lefts, mut rights) = (Vec::new(), Vec::new());
    let mut cur = t;
    while let Some(mut n) = cur {
        let m = own(&mut n);
        match m.item.key().cmp(key) {
            Ordering::Less => {
                cur = m.right.take();
                lefts.push((n, false));
            }
            Ordering::Greater => {
                cur = m.left.take();
                rights.push((n, true));
            }
            Ordering::Equal => unreachable!("split_loop is given a tree without the key"),
        }
    }
    (up_mut(lefts, None), up_mut(rights, None))
}

/// The tree made up from a path of nodes of this tree alone, root first, each with the child on
/// the path's side taken out (`true` for the left), and `bottom`, the subtree below the last:
/// each node given its child back, from the bottom, and refreshed. The in-place [`up`].
fn up_mut<I: Item>(path: Vec<(Arc<Node<I>>, bool)>, mut bottom: Tree<I>) -> Tree<I>
where
    I::Sum: Clone,
{
    for (mut n, left) in path.into_iter().rev() {
        let m = own(&mut n);
        if left {
            m.left = bottom;
        } else {
            m.right = bottom;
        }
        refresh(m);
        bottom = Some(n);
    }
    bottom
}

/// The items of `a` and of `b`, every key of `a` before every key of `b`: `join` in place,
/// `depth` calls below the walk's first.
#[inline]
fn join_mut<I: Item>(a: Tree<I>, b: Tree<I>, depth: usize) -> Tree<I>
where
    I::Sum: Clone,
{
    if depth >= DEEP {
        return join_loop(a, b);
    }
    match (a, b) {
        (None, x) | (x, None) => x,
        (Some(mut x), Some(mut y)) => {
            if above(&x, &y) {
                let m = own(&mut x);
                m.right = join_mut(m.right.take(), Some(y), depth + 1);
                refresh(m);
                Some(x)
            } else {
                let m = own(&mut y);
                m.left = join_mut(Some(x), m.left.take(), depth + 1);
                refresh(m);
                Some(y)
            }
        }
    }
}

/// [`join_mut`] by a loop: the spine walked down, the higher root taken each time with the
/// child on the other tree's side taken out and kept with that side, then the spine made up
/// from its bottom.
fn join_loop<I: Item>(a: Tree<I>, b: Tree<I>) -> Tree<I>
where
    I::Sum: Clone,
{
    // Each node of the spine, and whether the joined tree below it is its left child.
    let mut spine: Vec<(Arc<Node<I>>, bool)> = Vec::new();
    let (mut a, mut b) = (a, b);
    let bottom = loop {
        match (a, b) {
            (None, x) | (x, None) => break x,
            (Some(mut x), Some(mut y)) => {
                if above(&x, &y) {
                    a = own(&mut x).right.take();
                    b = Some(y);
                    spine.push((x, false));
                } else {
                    b = own(&mut y).left.take();
                    a = Some(x);
                    spine.push((y, true));
                }
            }
        }
    };
    up_mut(spine, bottom)
}

/// The item of `key`, to change, if the tree has it: one walk down, the nodes passed that another
/// tree shares copied first, `O(log n)`. The nodes are copied whether or not the key is found, so
/// a caller that may ask for an absent key in a shared tree asks [`get`] first. For items without
/// a summary only, since nothing above the item is made again after the change; the change must
/// keep the item's key and priority, which fix its place.
#[inline]
pub fn get_mut<'a, I, Q>(t: &'a mut Tree<I>, key: &Q) -> Option<&'a mut I>
where
    I: Item<Sum = ()>,
    I::Key: Borrow<Q>,
    Q: Ord + ?Sized,
{
    let mut t = t;
    loop {
        let n = own(t.as_mut()?);
        t = match key.cmp(n.item.key().borrow()) {
            Ordering::Less => &mut n.left,
            Ordering::Greater => &mut n.right,
            Ordering::Equal => return Some(&mut n.item),
        };
    }
}

/// Puts `item` into `t` in place of the item of its key, or adds it: [`insert`] in place.
#[inline]
pub fn insert_mut<I: Item>(t: &mut Tree<I>, item: I)
where
    I::Sum: Clone,
{
    let prio = item.priority();
    insert_at(t, item, prio, 0);
}

/// [`insert_mut`] of `item`, of priority `prio`, into the subtree `t`: the walk of `insert`, down
/// while the nodes stand above the new one, `depth` calls below the walk's first.
#[inline]
fn insert_at<I: Item>(t: &mut Tree<I>, item: I, prio: u64, depth: usize)
where
    I::Sum: Clone,
{
    if depth >= DEEP {
        *t = insert_loop(t.take(), item, prio);
        return;
    }
    match t {
        Some(n) if (n.prio, n.item.key()) > (prio, item.key()) => {
            let left = item.key() < n.item.key();
            let m = own(n);
            insert_at(
                if left { &mut m.left } else { &mut m.right },
                item,
                prio,
                depth + 1,
            );
            refresh(m);
        }
        Some(n) if n.item.key() == item.key() => {
            let m = own(n);
            m.item = item;
            refresh(m);
        }
        // The subtree split never holds the key: the proof is at `insert`, and `split_mut`
        // checks it.
        _ => {
            let (l, r) = split_mut(t.take(), item.key(), depth);
            *t = Some(node(item, prio, l, r));
        }
    }
}

/// [`insert_at`] by a loop: the nodes above the new one kept on a vector, each with the child on
/// the key's side taken out, then the tree made up again ([`up_mut`]).
fn insert_loop<I: Item>(t: Tree<I>, item: I, prio: u64) -> Tree<I>
where
    I::Sum: Clone,
{
    let mut path = Vec::new();
    let mut cur = t;
    let bottom = loop {
        match cur {
            Some(mut n) if (n.prio, n.item.key()) > (prio, item.key()) => {
                let left = item.key() < n.item.key();
                let m = own(&mut n);
                cur = if left { m.left.take() } else { m.right.take() };
                path.push((n, left));
            }
            Some(mut n) if n.item.key() == item.key() => {
                let m = own(&mut n);
                m.item = item;
                refresh(m);
                break Some(n);
            }
            rest => {
                let (l, r) = split_loop(rest, item.key());
                break Some(node(item, prio, l, r));
            }
        }
    };
    up_mut(path, bottom)
}

/// Takes the item of `key` out of `t`, if it has one: [`remove`] in place. A tree without the key
/// is left as it is, none of its nodes copied.
#[inline]
pub fn remove_mut<I: Item, Q: Ord + ?Sized>(t: &mut Tree<I>, key: &Q)
where
    I::Key: Borrow<Q>,
    I::Sum: Clone,
{
    if get(t, key).is_some() {
        remove_at(t, key, 0);
    }
}

/// The children of `n`, the node [`remove_at`] takes out. It is not copied: its children are
/// taken from it if this tree alone holds it, and shared with the other tree otherwise.
fn children<I: Item>(n: &mut Arc<Node<I>>) -> (Tree<I>, Tree<I>) {
    match Arc::get_mut(n) {
        Some(m) => (m.left.take(), m.right.take()),
        None => (n.left.clone(), n.right.clone()),
    }
}

/// [`remove_mut`] of `key` from the subtree `t`, which holds it, `depth` calls below the walk's
/// first.
#[inline]
fn remove_at<I: Item, Q: Ord + ?Sized>(t: &mut Tree<I>, key: &Q, depth: usize)
where
    I::Key: Borrow<Q>,
    I::Sum: Clone,
{
    if depth >= DEEP {
        *t = remove_loop(t.take(), key);
        return;
    }
    let n = t.as_mut().expect("remove_mut found the key above");
    match key.cmp(n.item.key().borrow()) {
        Ordering::Equal => {
            let (l, r) = children(n);
            *t = join_mut(l, r, depth);
        }
        side => {
            let left = side == Ordering::Less;
            let m = own(n);
            remove_at(
                if left { &mut m.left } else { &mut m.right },
                key,
                depth + 1,
            );
            refresh(m);
        }
    }
}

/// [`remove_at`] by a loop: the nodes above the key kept on a vector, each with the child on the
/// key's side taken out, then the tree made up again ([`up_mut`]).
fn remove_loop<I: Item, Q: Ord + ?Sized>(t: Tree<I>, key: &Q) -> Tree<I>
where
    I::Key: Borrow<Q>,
    I::Sum: Clone,
{
    let mut path = Vec::new();
    let mut cur = t;
    let bottom = loop {
        let mut n = cur.expect("remove_mut found the key above");
        match key.cmp(n.item.key().borrow()) {
            Ordering::Equal => {
                let (l, r) = children(&mut n);
                break join_loop(l, r);
            }
            side => {
                let left = side == Ordering::Less;
                let m = own(&mut n);
                cur = if left { m.left.take() } else { m.right.take() };
                path.push((n, left));
            }
        }
    };
    up_mut(path, bottom)
}

pub mod lazy;

#[cfg(test)]
mod tests;
