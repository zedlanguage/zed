//! The Cartesian tree of items given in key order, built bottom up in `O(n)`
//! (DRY-persistent-structures: one build, used by zed-kernel's `bdd::set::from_sorted` and
//! `bdd::settings::from_keys`, which each held a copy of it until 2026-11-24).
//!
//! The tree is a max-heap on `(priority, key)`: the root is the item of greatest priority, ties
//! broken by the greater key, and its left and right subtrees are the trees of the items before
//! and after it. A treap whose priorities come from its keys has this shape whatever the order
//! the keys were put in, so the build gives the treap that putting the keys in one at a time
//! gives.
//!
//! Sources. The Cartesian tree: J. Vuillemin, "A unifying look at data structures", CACM
//! 23(4), 229-239, 1980, doi:10.1145/358841.358852, section 3.1: the root is the point of
//! least `y`, its left and right subtrees the Cartesian trees of the points left and right of
//! it in `x` (here `x` is the key and the root is the highest priority). The construction in
//! `O(n)`: H. N. Gabow, J. L. Bentley and R. E. Tarjan, "Scaling and related techniques for
//! geometry problems", STOC 1984, 135-143, doi:10.1145/800057.808675, section 3: "Ti is
//! derived from Ti-1 by ascending along the rightmost path of Ti-1 until xl, the first node
//! larger than xi, is found; the right subtree of xl is made into the left subtree of xi, and
//! xi is made the right child of xl. The total time to construct Tn = T is O(n), since a node
//! leaves the rightmost path immediately after it is traversed." Here `spine` is that
//! rightmost path and `passed` the right subtree of the node stopped at. Both texts were read
//! and both DOIs and page ranges confirmed with Crossref on 2026-11-19 by the writer of the
//! comment at `bdd::set::from_sorted`, which this one moves unchanged in substance.
//!
//! Proof that [`build`] makes that tree, by induction on `i`: after item `i` is placed, the
//! links among items `0..=i` are the Cartesian tree of those items and `spine` is its right
//! path, root first, with `(priority, key)` strictly decreasing down it.
//! 1. Before item 0 the tree is empty and so is `spine`.
//! 2. Item `i` comes after every item placed, so in the tree of `0..=i` it lies on the right
//!    path, below every item of the right path that is greater than it, and above every
//!    one that is less (a heap); the items of the right path less than it are a suffix of
//!    `spine`, as `spine` decreases. The loop pops exactly that suffix.
//! 3. The last item popped, `passed`, roots the subtree of the items between the item stopped
//!    at (or the start) and `i`: all lie before `i` in key order, and they are less than `i`,
//!    so they form `i`'s left subtree, and `left[i] = passed` makes it so. Item `i` has no
//!    right subtree yet, as no later item is placed.
//! 4. The item stopped at, if any, is greater than `i` and is the lowest such on the right
//!    path, so `i` is its right child; `right[top] = i` replaces the old right child, which is
//!    `passed`, now under `i`. With no item stopped at, `i` is the root.
//! 5. Pushing `i` keeps `spine` the right path of the new tree, decreasing down it. ∎
//!
//! Cost: each item is pushed once and popped at most once, so the loop does `O(n)` steps, as
//! Gabow, Bentley and Tarjan say; the nodes are then made in post-order by one explicit stack,
//! each once, so no recursion as deep as the tree (which is `n` deep when the priorities rise
//! with the keys) is ever made. Comparisons of `(priority, key)` pairs are `O(1)` for the
//! users here (`u64` priorities, keys compared by a small value). Tested by
//! `tests::the_build_is_the_recursive_definition` and the benchmark
//! `bench::a_cartesian_build_takes_linear_time`.
//
// Complexity tradeoff: two index arrays of `n` entries are made before any node, `O(n)` words
// of memory beside the nodes, so that each node is made once over children already made (a
// persistent node cannot be changed after it is made). Putting the items in one at a time
// makes no such arrays but makes `O(n log n)` nodes in expectation.

/// The Cartesian tree of `keys`, sorted strictly increasing, with priority `prios[i]` for
/// `keys[i]`: each node made once, after its children, by `make(i, key, left, right)`. `None`
/// when `keys` is empty. Proof and cost at the head of this module.
pub fn build<K: Ord, P: Ord, T>(
    keys: Vec<K>,
    prios: &[P],
    mut make: impl FnMut(usize, K, Option<T>, Option<T>) -> T,
) -> Option<T> {
    assert_eq!(keys.len(), prios.len(), "a priority for each key");
    debug_assert!(
        keys.windows(2).all(|w| w[0] < w[1]),
        "keys strictly increasing"
    );
    const NONE: usize = usize::MAX;
    let n = keys.len();
    let (mut left, mut right) = (vec![NONE; n], vec![NONE; n]);
    // The right path of the tree of the items so far, root first.
    let mut spine: Vec<usize> = Vec::new();
    for i in 0..n {
        let mut passed = NONE;
        while let Some(&top) = spine.last() {
            if (&prios[top], &keys[top]) < (&prios[i], &keys[i]) {
                passed = top;
                spine.pop();
            } else {
                break;
            }
        }
        left[i] = passed;
        if let Some(&top) = spine.last() {
            right[top] = i;
        }
        spine.push(i);
    }
    let root = *spine.first()?;
    let mut keys: Vec<Option<K>> = keys.into_iter().map(Some).collect();
    let mut made: Vec<Option<T>> = (0..n).map(|_| None).collect();
    let mut todo = vec![(root, false)];
    while let Some((i, ready)) = todo.pop() {
        if ready {
            let l = (left[i] != NONE).then(|| made[left[i]].take()).flatten();
            let r = (right[i] != NONE).then(|| made[right[i]].take()).flatten();
            let key = keys[i].take().expect("each key made once");
            made[i] = Some(make(i, key, l, r));
            continue;
        }
        todo.push((i, true));
        for c in [right[i], left[i]] {
            if c != NONE {
                todo.push((c, false));
            }
        }
    }
    made[root].take()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A tree of keys, for the tests.
    #[derive(Debug, PartialEq)]
    enum Tree {
        Leaf,
        Node(Box<Tree>, u32, Box<Tree>),
    }

    fn built(keys: &[u32], prios: &[u64]) -> Tree {
        build(keys.to_vec(), prios, |_, k, l, r| {
            Tree::Node(
                Box::new(l.unwrap_or(Tree::Leaf)),
                k,
                Box::new(r.unwrap_or(Tree::Leaf)),
            )
        })
        .unwrap_or(Tree::Leaf)
    }

    /// The definition: the root is the item of greatest `(priority, key)`, its subtrees the
    /// trees of the items on each side of it. Quadratic at worst; for the tests only.
    fn defined(keys: &[u32], prios: &[u64]) -> Tree {
        let Some(top) = (0..keys.len()).max_by_key(|&i| (prios[i], keys[i])) else {
            return Tree::Leaf;
        };
        Tree::Node(
            Box::new(defined(&keys[..top], &prios[..top])),
            keys[top],
            Box::new(defined(&keys[top + 1..], &prios[top + 1..])),
        )
    }

    /// Random priorities from a small range, so that many tie and the key decides, for every
    /// `n` up to 60, 20 draws each.
    #[test]
    fn the_build_is_the_recursive_definition() {
        let (mut rng, _) = crate::seed::Rng::fresh("the_build_is_the_recursive_definition");
        for n in 0..=60u32 {
            for _ in 0..20 {
                let keys: Vec<u32> = (0..n).map(|i| 3 * i + 1).collect();
                let prios: Vec<u64> = (0..n).map(|_| rng.below_u64(8)).collect();
                assert_eq!(built(&keys, &prios), defined(&keys, &prios), "{prios:?}");
            }
        }
    }

    /// Corners: no key, one key, and priorities that rise, fall or all tie, which make a path
    /// as deep as the input (100 000 deep, built with no recursion), and the order each node
    /// is made in: children first.
    #[test]
    fn corners_and_deep_paths() {
        assert_eq!(
            build(Vec::<u32>::new(), &[] as &[u64], |_, k, _, _| k),
            None
        );
        assert_eq!(built(&[5], &[9]), defined(&[5], &[9]));
        let n = 100_000u32;
        let keys: Vec<u32> = (0..n).collect();
        let rising: Vec<u64> = (0..n as u64).collect();
        let falling: Vec<u64> = rising.iter().rev().copied().collect();
        let tied = vec![7u64; n as usize];
        for (prios, root) in [(&rising, n - 1), (&falling, 0), (&tied, n - 1)] {
            // The depth and the root, counted as the nodes are made.
            let made = build(keys.clone(), prios, |_, k, l: Option<(u32, u32)>, r| {
                let depth = 1 + l.map_or(0, |x| x.1).max(r.map_or(0, |x| x.1));
                (k, depth)
            });
            assert_eq!(made, Some((root, n)));
        }
        let mut order = Vec::new();
        build(vec![1u32, 2, 3], &[1u64, 3, 2], |i, _, l, r| {
            order.push((i, l.is_some(), r.is_some()));
        });
        assert_eq!(
            order,
            [(0, false, false), (2, false, false), (1, true, true)]
        );
    }
}
