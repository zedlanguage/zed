//! A persistent join-based AVL tree of items in sequence order, each node keeping the height, the
//! number of items and a summary of its subtree ([`Item::sum`]). Every operation is built from
//! [`join`] (G. E. Blelloch, D. Ferizovic and Y. Sun, "Just Join for Parallel Ordered Sets", SPAA
//! 2016, pp. 253-264, doi:10.1145/2935764.2935768; arXiv:1602.02120), section 3 ("The JOIN
//! Function"), the AVL figure: join(TL, k, TR) is joinRight when h(TL) > h(TR) + 1, joinLeft when
//! h(TR) > h(TL) + 1, and node(TL, k, TR) otherwise; joinRight walks down the right spine of TL
//! to the first subtree c with h(c) <= h(TR) + 1, puts node(c, k, TR) there, and on the way back
//! up makes one single or double rotation where a node's right side has grown two taller than
//! its left. `join_right` and `join_left` follow the figure line for line. Its cost is
//! O(|h(TL) - h(TR)| + 1) (the paper's theorem for AVL trees), and split and the set operations
//! are built from join alone (section 4 and Figure 1). Checked 2026-11-20 (zedc-lattice
//! `interval.rs`, where this code was first): the DOI, venue and pages on Crossref; the arXiv
//! LaTeX source read (the figure, section 4 and the theorem). Departures: nodes are shared, not
//! changed in place, so a new node is made where the paper rotates, and a node whose last handle
//! an operation holds is taken apart, not copied ([`parts`]); nothing runs in parallel.
//!
//! The tree has no keys of its own: the order is the order the items were joined in, so it is a
//! sequence (zedc-presburger `extend/plane.rs`, the sides of a hull) or, when every builder keeps
//! the items sorted, an ordered set (zedc-lattice `interval.rs`, the pieces of a set), split by a
//! predicate that holds on a prefix ([`split`]). An AVL tree of `n` items has height at most
//! `1.4405 log2(n + 2)` (G. M. Adelson-Velsky and E. M. Landis, 1962; D. E. Knuth, TAOCP vol. 3,
//! 2nd ed., section 6.2.3, Theorem A: `h < 1.4405 lg(N + 2) - 0.3277`; quoted from memory, not
//! checked against the text in this change), below 93 for every `n < 2^64`, so a height is a
//! `u8`, and the recursions here and the drop the compiler makes are at most that deep whatever
//! the items.
//!
//! Tested by `avl::tests`: every operation against a `Vec` on random sequences, and on every
//! result that the two heights of each node differ by at most 1 and that its height, length and
//! summary are right. No test here measures the work; the benches of the users do.

use std::fmt;
use std::sync::Arc;

/// An item of an AVL tree and the summary of a subtree it is the root of.
pub trait Item: Clone {
    /// What each node keeps of its subtree beside the height and the length; `()` for none.
    type Sum;
    /// The summary of a subtree with this item at its root over children of summaries `left`
    /// and `right` (`None`: no child). Called once for each node made, so a meter of the nodes
    /// made may count there.
    fn sum(&self, left: Option<&Self::Sum>, right: Option<&Self::Sum>) -> Self::Sum;
}

/// A node: its item, the height, the number of items and the summary of its subtree, and the
/// trees of the items before and after it.
pub struct Node<I: Item> {
    item: I,
    height: u8,
    len: usize,
    sum: I::Sum,
    left: Tree<I>,
    right: Tree<I>,
}

/// A tree: its root, or `None` when empty.
pub type Tree<I> = Option<Arc<Node<I>>>;

impl<I: Item> Node<I> {
    /// The node's item.
    #[inline]
    pub fn item(&self) -> &I {
        &self.item
    }

    /// The items before the node's.
    #[inline]
    pub fn left(&self) -> &Tree<I> {
        &self.left
    }

    /// The items after the node's.
    #[inline]
    pub fn right(&self) -> &Tree<I> {
        &self.right
    }

    /// The summary of the node's subtree.
    #[inline]
    pub fn sum(&self) -> &I::Sum {
        &self.sum
    }

    /// The height of the node's subtree, 1 for a leaf.
    #[inline]
    pub fn height(&self) -> u8 {
        self.height
    }

    /// The number of items of the node's subtree, at least 1.
    #[inline]
    pub fn size(&self) -> usize {
        self.len
    }
}

/// The items of the subtree in order, as a list.
impl<I: Item + fmt::Debug> fmt::Debug for Node<I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn items<'a, I: Item>(t: &'a Tree<I>, out: &mut Vec<&'a I>) {
            if let Some(n) = t {
                items(&n.left, out);
                out.push(&n.item);
                items(&n.right, out);
            }
        }
        let mut out = Vec::with_capacity(self.len);
        items(&self.left, &mut out);
        out.push(&self.item);
        items(&self.right, &mut out);
        f.debug_list().entries(out).finish()
    }
}

/// The height of `t`, 0 when empty.
#[inline]
pub fn height<I: Item>(t: &Tree<I>) -> u8 {
    t.as_ref().map_or(0, |n| n.height)
}

/// The number of items of `t`.
#[inline]
pub fn len<I: Item>(t: &Tree<I>) -> usize {
    t.as_ref().map_or(0, |n| n.len)
}

/// The node of `item` over `left` and `right`, its height, length and summary made from
/// theirs: `O(1)` and one [`Item::sum`]. The caller keeps the balance: [`join`] does.
#[inline]
pub fn node<I: Item>(left: Tree<I>, item: I, right: Tree<I>) -> Arc<Node<I>> {
    // The summary is made inside the literal (its fields are made in the order written, so
    // before `item` moves), as zedc-lattice's tree of pieces made its totals before its move
    // here, rather than in a local moved in after.
    Arc::new(Node {
        height: 1 + height(&left).max(height(&right)),
        len: len(&left) + len(&right) + 1,
        sum: item.sum(
            left.as_deref().map(|n| &n.sum),
            right.as_deref().map(|n| &n.sum),
        ),
        item,
        left,
        right,
    })
}

/// The children and the item of `n`, moved out when `n` is not shared and cloned when it is.
#[inline]
pub fn parts<I: Item>(n: Arc<Node<I>>) -> (Tree<I>, I, Tree<I>) {
    match Arc::try_unwrap(n) {
        Ok(n) => (n.left, n.item, n.right),
        Err(n) => (n.left.clone(), n.item.clone(), n.right.clone()),
    }
}

#[inline]
fn rotate_left<I: Item>(t: Arc<Node<I>>) -> Arc<Node<I>> {
    let (a, x, r) = parts(t);
    let (b, y, c) = parts(r.expect("a right child to rotate"));
    node(Some(node(a, x, b)), y, c)
}

#[inline]
fn rotate_right<I: Item>(t: Arc<Node<I>>) -> Arc<Node<I>> {
    let (l, y, c) = parts(t);
    let (a, x, b) = parts(l.expect("a left child to rotate"));
    node(a, x, Some(node(b, y, c)))
}

/// The tree of `l`'s items, then `k`, then `r`'s: `O(|height(l) - height(r)| + 1)`, of height at
/// most `max(height(l), height(r)) + 1` (the paper's Lemma 1; the citation is at the head of the
/// module).
#[inline]
pub fn join<I: Item>(l: Tree<I>, k: I, r: Tree<I>) -> Arc<Node<I>> {
    let (hl, hr) = (height(&l), height(&r));
    match (l, r) {
        (Some(l), r) if hl > hr + 1 => join_right(l, k, r),
        (l, Some(r)) if hr > hl + 1 => join_left(l, k, r),
        (l, r) => node(l, k, r),
    }
}

/// Proof that the `expect`s here and in the rotations cannot fire (`h` is [`height`], 0 for
/// `None`; `tl` is a valid AVL tree, as every tree built by [`node`] through [`join`] is, which
/// the tests' `check` asserts on every result). Precondition: `h(tl) > h(tr) + 1`; [`join`]
/// calls with it, and the recursive call below with `h(c) > h(tr) + 1`. (1) `c.expect`: in the
/// `else` branch `h(c) > h(tr) + 1 >= 1`, so `c` is `Some`. (2) `rotate_right(t)`, `t =
/// node(c, k, tr)`, needs `c` to be `Some`. Balance of `tl` gives `max(h(l), h(c)) = h(tl) - 1`
/// and `|h(l) - h(c)| <= 1`; as `h(c) <= h(tr) + 1 <= h(tl) - 1`, `h(l) >= h(tl) - 2 >= h(tr)`.
/// The rotation is taken when `h(t) = max(h(c), h(tr)) + 1 > h(l) + 1`; `h(tr) <= h(l)` rules
/// out `h(tr)` as the maximum, so `h(c) > h(l) >= 0`, and `c` is `Some`. (3) The outer
/// `rotate_left`, and the one in the `else` branch, rotate a node built here with `Some` as
/// its right child. The same proof, mirrored, holds for [`join_left`].
#[inline]
fn join_right<I: Item>(tl: Arc<Node<I>>, k: I, tr: Tree<I>) -> Arc<Node<I>> {
    let (l, x, c) = parts(tl);
    if height(&c) <= height(&tr) + 1 {
        let t = node(c, k, tr);
        if t.height <= height(&l) + 1 {
            node(l, x, Some(t))
        } else {
            rotate_left(node(l, x, Some(rotate_right(t))))
        }
    } else {
        let t = join_right(c.expect("taller than tr"), k, tr);
        let tall = t.height > height(&l) + 1;
        let t = node(l, x, Some(t));
        if tall { rotate_left(t) } else { t }
    }
}

#[inline]
fn join_left<I: Item>(tl: Tree<I>, k: I, tr: Arc<Node<I>>) -> Arc<Node<I>> {
    let (c, x, r) = parts(tr);
    if height(&c) <= height(&tl) + 1 {
        let t = node(tl, k, c);
        if t.height <= height(&r) + 1 {
            node(Some(t), x, r)
        } else {
            rotate_right(node(Some(rotate_left(t)), x, r))
        }
    } else {
        let t = join_left(tl, k, c.expect("taller than tl"));
        let tall = t.height > height(&r) + 1;
        let t = node(Some(t), x, r);
        if tall { rotate_right(t) } else { t }
    }
}

/// The items of `t` on which `goes_left` holds, and the rest, for `goes_left` true on a prefix
/// of the items and false after it. `O(height(t))`: the joins on the way back up take pieces of
/// growing height, and their costs `|h(a) - h(b)| + 1` add up to `O(height(t))` (the paper's
/// bound of split, section 4).
#[inline]
pub fn split<I: Item>(t: Tree<I>, goes_left: &impl Fn(&I) -> bool) -> (Tree<I>, Tree<I>) {
    let Some(n) = t else {
        return (None, None);
    };
    let left = goes_left(&n.item);
    let (l, k, r) = parts(n);
    if left {
        let (rl, rr) = split(r, goes_left);
        (Some(join(l, k, rl)), rr)
    } else {
        let (ll, lr) = split(l, goes_left);
        (ll, Some(join(lr, k, r)))
    }
}

/// The tree without its last item, and that item: `O(height(t))`.
#[inline]
pub fn split_last<I: Item>(t: Arc<Node<I>>) -> (Tree<I>, I) {
    let (l, k, r) = parts(t);
    match r {
        None => (l, k),
        Some(r) => {
            let (r, last) = split_last(r);
            (Some(join(l, k, r)), last)
        }
    }
}

/// The tree without its first item, and that item: `O(height(t))`.
#[inline]
pub fn split_first<I: Item>(t: Arc<Node<I>>) -> (I, Tree<I>) {
    let (l, k, r) = parts(t);
    match l {
        None => (k, r),
        Some(l) => {
            let (first, l) = split_first(l);
            (first, Some(join(l, k, r)))
        }
    }
}

/// `l`'s items then `r`'s: one [`split_first`] and one [`join`], `O(height(l) + height(r))`.
#[inline]
pub fn concat<I: Item>(l: Tree<I>, r: Tree<I>) -> Tree<I> {
    match (l, r) {
        (l, None) => l,
        (None, r) => r,
        (l, Some(r)) => {
            let (k, r) = split_first(r);
            Some(join(l, k, r))
        }
    }
}

/// A balanced tree of `items`, in order: `O(n)`, one [`node`] an item. The two halves of a
/// node differ by at most one item, so its heights by at most 1.
#[inline]
pub fn from_slice<I: Item>(items: &[I]) -> Tree<I> {
    if items.is_empty() {
        return None;
    }
    let m = items.len() / 2;
    Some(node(
        from_slice(&items[..m]),
        items[m].clone(),
        from_slice(&items[m + 1..]),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// An item with a summary that is the sum and the first and last of its subtree, so that a
    /// wrong order or a stale summary shows.
    #[derive(Clone, Debug, PartialEq)]
    struct V(u64);

    impl Item for V {
        type Sum = (u64, u64, u64);
        fn sum(&self, l: Option<&Self::Sum>, r: Option<&Self::Sum>) -> Self::Sum {
            let total = l.map_or(0, |s| s.0) + self.0 + r.map_or(0, |s| s.0);
            (total, l.map_or(self.0, |s| s.1), r.map_or(self.0, |s| s.2))
        }
    }

    fn listed(t: &Tree<V>, out: &mut Vec<u64>) {
        if let Some(n) = t {
            listed(&n.left, out);
            out.push(n.item.0);
            listed(&n.right, out);
        }
    }

    fn list(t: &Tree<V>) -> Vec<u64> {
        let mut out = Vec::new();
        listed(t, &mut out);
        out
    }

    /// Asserts the balance and the stored height, length and summary of every node of `t`.
    fn check(t: &Tree<V>) {
        let Some(n) = t else { return };
        check(&n.left);
        check(&n.right);
        let (hl, hr) = (height(&n.left), height(&n.right));
        assert!(hl.abs_diff(hr) <= 1, "unbalanced: {hl} and {hr}");
        assert_eq!(n.height, hl.max(hr) + 1);
        assert_eq!(n.len, len(&n.left) + len(&n.right) + 1);
        let items = list(t);
        let want = (items.iter().sum(), items[0], items[items.len() - 1]);
        assert_eq!(n.sum, want);
    }

    /// splitmix64, so that the tests draw the same sequences in every run.
    fn next(s: &mut u64) -> u64 {
        *s = s.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = *s;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn build(xs: &[u64]) -> Tree<V> {
        let items: Vec<V> = xs.iter().map(|&x| V(x)).collect();
        from_slice(&items)
    }

    #[test]
    fn joins_splits_and_concats_agree_with_a_vec() {
        let mut s = 7;
        for round in 0..400 {
            let n = (next(&mut s) % 70) as usize;
            let m = (next(&mut s) % 70) as usize;
            let a: Vec<u64> = (0..n).map(|_| next(&mut s) % 1000).collect();
            let b: Vec<u64> = (0..m).map(|_| next(&mut s) % 1000).collect();
            let (ta, tb) = (build(&a), build(&b));
            check(&ta);
            assert_eq!(list(&ta), a);
            let k = next(&mut s) % 1000;
            let joined = Some(join(ta.clone(), V(k), tb.clone()));
            check(&joined);
            let mut want = a.clone();
            want.push(k);
            want.extend(&b);
            assert_eq!(list(&joined), want, "round {round}");
            assert!(height(&joined) <= height(&ta).max(height(&tb)) + 1);
            let both = concat(ta.clone(), tb.clone());
            check(&both);
            let mut ab = a.clone();
            ab.extend(&b);
            assert_eq!(list(&both), ab);
            // A split at every position, by a predicate on the position, which holds on a prefix.
            let at = (next(&mut s) as usize) % (want.len() + 1);
            let indexed: Vec<V> = (0..want.len() as u64).map(V).collect();
            let (l, r) = split(from_slice(&indexed), &|v: &V| (v.0 as usize) < at);
            check(&l);
            check(&r);
            assert_eq!(len(&l), at);
            assert_eq!(len(&r), want.len() - at);
            if let Some(t) = joined {
                let (rest, last) = split_last(t.clone());
                check(&rest);
                assert_eq!(last.0, *want.last().unwrap());
                assert_eq!(list(&rest), want[..want.len() - 1]);
                let (first, rest) = split_first(t);
                check(&rest);
                assert_eq!(first.0, want[0]);
                assert_eq!(list(&rest), want[1..]);
            }
            // The operands are left as they were: the operations share, never change, a node.
            assert_eq!(list(&ta), a);
            assert_eq!(list(&tb), b);
        }
    }

    #[test]
    fn joining_a_short_tree_to_a_tall_one_keeps_the_balance() {
        let tall: Vec<u64> = (0..5000).collect();
        let mut t = build(&tall);
        for k in 0..300 {
            t = Some(join(t, V(10_000 + k), None));
            t = Some(join(None, V(20_000 + k), t));
        }
        check(&t);
        assert_eq!(len(&t), 5600);
        // Adelson-Velsky and Landis's bound, 1.4405 log2(n + 2), is about 18.0 at n = 5600.
        assert!(height(&t) <= 18, "height {}", height(&t));
    }
}
