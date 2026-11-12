//! The rows of a hull by their pivots, in a persistent treap whose shape depends only on the
//! pivots it holds: each node's priority is a hash of its pivot, ties broken by the pivot's
//! order. A map made from another by a few changes copies the paths to the changed pivots and
//! shares every other subtree with it, and since both have the one shape their keys give, the
//! subtrees they share sit at the same places in both. The difference of the two is found by a
//! walk that passes over a shared subtree at once.

use std::cmp::Ordering;
use std::fmt;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::sync::Arc;

use crate::presburger::{Atom, Lin};

type Tree = Option<Arc<Node>>;

#[derive(Clone)]
struct Node {
    key: Atom,
    val: Arc<Lin>,
    prio: u64,
    left: Tree,
    right: Tree,
}

/// A deterministic splitmix64 priority from a pivot.
fn prio_of(key: &Atom) -> u64 {
    let mut h = DefaultHasher::new();
    key.hash(&mut h);
    let mut z = h.finish().wrapping_add(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// The order of the nodes from the root down: by priority, then by pivot, so no two nodes of a
/// map tie and one set of pivots has one shape.
fn rank(n: &Node) -> (u64, &Atom) {
    (n.prio, &n.key)
}

// Complexity tradeoff: standard implementation, the rows in an `imbl` 7.0.2 `OrdMap` (a B-tree
// of 16 keys a node) compared with its `diff`, whose cursor passes over a shared subtree only
// after it has gone down to that subtree's first leaf, and looks at each of up to 17 children of
// every copied node: Θ(16 · depth²) a join of hulls that differ in one row, measured 7.0K, 8.2K,
// 12.0K and 14.5K instructions a join at 256, 512, 1,024 and 2,048 rows (2.06 times from 256 to
// 2,048, where log n grows 1.375 times). Used: a treap whose shape its pivots fix, and a diff
// that compares the subtrees at the fronts of the two walks by identity and passes over one the
// two maps share in one step: O((k + 1) · depth) for k differing rows, depth O(log n) expected
// (about 1.39 log2 n), measured 8.9K, 8.9K, 10.7K and 9.9K instructions a join at 256 to 2,048
// rows (1.11 times). Tradeoffs: the bounds are expected ones, over the hash of the pivots, not
// worst-case ones; a change copies a path of about 1.39 log2 n nodes of one row each, where the
// B-tree copied about log16 n nodes of 16; insert, remove and drop recurse on the depth; and two
// maps that hold equal rows in nodes they do not share are compared row by row, which costs
// their size, as the B-tree's diff did. The answers are the same. Tests
// `l01_39_reduced_product::hull::a_join_costs_near_the_rows_that_differ` and
// `a_join_costs_near_the_rows_that_differ_wherever_they_sort`; COMPLEXITY.md S26.
/// The rows of a hull by their pivots.
#[derive(Clone, Default)]
pub(super) struct Rows {
    root: Tree,
}

impl Rows {
    /// The row of `key`. O(depth).
    pub(super) fn get(&self, key: &Atom) -> Option<&Arc<Lin>> {
        let mut t = self.root.as_deref();
        while let Some(n) = t {
            t = match key.cmp(&n.key) {
                Ordering::Less => n.left.as_deref(),
                Ordering::Greater => n.right.as_deref(),
                Ordering::Equal => return Some(&n.val),
            };
        }
        None
    }

    /// The row of `key`, which the map holds, to change. The nodes on the path to it that the
    /// map shares with another are copied first. O(depth).
    pub(super) fn get_mut(&mut self, key: &Atom) -> Option<&mut Arc<Lin>> {
        let mut t = &mut self.root;
        loop {
            let n = Arc::make_mut(t.as_mut()?);
            t = match key.cmp(&n.key) {
                Ordering::Less => &mut n.left,
                Ordering::Greater => &mut n.right,
                Ordering::Equal => return Some(&mut n.val),
            };
        }
    }

    /// Puts `val` at `key`, in place of any row there. O(depth) expected.
    pub(super) fn insert(&mut self, key: Atom, val: Arc<Lin>) {
        let prio = prio_of(&key);
        insert(
            &mut self.root,
            Node {
                key,
                val,
                prio,
                left: None,
                right: None,
            },
        );
    }

    /// Takes out the row of `key`, if there is one. O(depth) expected.
    pub(super) fn remove(&mut self, key: &Atom) {
        remove(&mut self.root, key);
    }

    /// The rows, in pivot order.
    pub(super) fn values(&self) -> impl Iterator<Item = &Arc<Lin>> {
        self.nodes().map(|n| &n.val)
    }

    /// The nodes, in pivot order.
    fn nodes(&self) -> Nodes<'_> {
        let mut it = Nodes { stack: Vec::new() };
        it.down(self.root.as_deref());
        it
    }

    /// Calls `f` on each pivot whose row differs between `self` and `other`, in pivot order,
    /// with the pivot and row of `self` and the row of `other`, either absent where that map
    /// has no row there. Rows are compared by value. O((k + 1) · depth) expected, for k
    /// differing rows, when the two maps share their other subtrees.
    pub(super) fn diff<'a>(
        &'a self,
        other: &'a Rows,
        mut f: impl FnMut(Option<(&'a Atom, &'a Arc<Lin>)>, Option<&'a Arc<Lin>>),
    ) {
        let start = |t: &'a Tree| t.as_deref().map(Step::Tree).into_iter().collect();
        let (mut a, mut b): (Vec<Step<'a>>, Vec<Step<'a>>) =
            (start(&self.root), start(&other.root));
        loop {
            match (a.last().copied(), b.last().copied()) {
                (None, None) => return,
                (Some(Step::Tree(x)), Some(Step::Tree(y))) => {
                    if std::ptr::eq(x, y) {
                        a.pop();
                        b.pop();
                    } else {
                        // The higher of the two roots holds pivots the other's subtree may
                        // also hold below its own root, so it is opened first; two roots of one
                        // pivot are at one place in both shapes and are opened together.
                        match rank(x).cmp(&rank(y)) {
                            Ordering::Greater => open(&mut a),
                            Ordering::Less => open(&mut b),
                            Ordering::Equal => {
                                open(&mut a);
                                open(&mut b);
                            }
                        }
                    }
                }
                (Some(Step::Tree(_)), _) => open(&mut a),
                (_, Some(Step::Tree(_))) => open(&mut b),
                (Some(Step::Entry(x)), Some(Step::Entry(y))) => match x.key.cmp(&y.key) {
                    Ordering::Less => {
                        a.pop();
                        f(Some((&x.key, &x.val)), None);
                    }
                    Ordering::Greater => {
                        b.pop();
                        f(None, Some(&y.val));
                    }
                    Ordering::Equal => {
                        a.pop();
                        b.pop();
                        if !Arc::ptr_eq(&x.val, &y.val) && x.val != y.val {
                            f(Some((&x.key, &x.val)), Some(&y.val));
                        }
                    }
                },
                (Some(Step::Entry(x)), None) => {
                    a.pop();
                    f(Some((&x.key, &x.val)), None);
                }
                (None, Some(Step::Entry(y))) => {
                    b.pop();
                    f(None, Some(&y.val));
                }
            }
        }
    }
}

impl fmt::Debug for Rows {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map()
            .entries(self.nodes().map(|n| (&n.key, &n.val)))
            .finish()
    }
}

/// What a diff's walk of one map has still to visit, the next on top: a whole subtree, or one
/// node's row alone (its left subtree visited, its right one below it on the stack).
#[derive(Clone, Copy)]
enum Step<'a> {
    Tree(&'a Node),
    Entry(&'a Node),
}

/// Replaces the subtree on top of `stack` by its left subtree, its root's row and its right
/// subtree, the left on top.
fn open(stack: &mut Vec<Step<'_>>) {
    let Some(Step::Tree(n)) = stack.pop() else {
        unreachable!("a subtree on top of the walk");
    };
    stack.extend(n.right.as_deref().map(Step::Tree));
    stack.push(Step::Entry(n));
    stack.extend(n.left.as_deref().map(Step::Tree));
}

/// The nodes of a map in pivot order, by a stack of the nodes whose left subtrees are being
/// visited.
struct Nodes<'a> {
    stack: Vec<&'a Node>,
}

impl<'a> Nodes<'a> {
    /// Pushes `t` and its left children, down to the first node of `t`.
    fn down(&mut self, mut t: Option<&'a Node>) {
        while let Some(n) = t {
            self.stack.push(n);
            t = n.left.as_deref();
        }
    }
}

impl<'a> Iterator for Nodes<'a> {
    type Item = &'a Node;

    fn next(&mut self) -> Option<&'a Node> {
        let n = self.stack.pop()?;
        self.down(n.right.as_deref());
        Some(n)
    }
}

/// Puts the node `new`, which has no children, into `t`, in place of the node of its pivot if
/// there is one, copying the shared nodes on the path to it.
fn insert(t: &mut Tree, new: Node) {
    let Some(n) = t else {
        *t = Some(Arc::new(new));
        return;
    };
    let side = new.key.cmp(&n.key);
    if side == Ordering::Equal {
        Arc::make_mut(n).val = new.val;
    } else if rank(&new) > rank(n) {
        let (left, right) = split(t.take(), &new.key);
        *t = Some(Arc::new(Node { left, right, ..new }));
    } else {
        let n = Arc::make_mut(n);
        insert(
            if side == Ordering::Less {
                &mut n.left
            } else {
                &mut n.right
            },
            new,
        );
    }
}

/// The nodes of `t` with pivots below `key`, which `t` does not hold, and those above.
fn split(t: Tree, key: &Atom) -> (Tree, Tree) {
    let Some(mut n) = t else {
        return (None, None);
    };
    let m = Arc::make_mut(&mut n);
    if m.key < *key {
        let (below, above) = split(m.right.take(), key);
        m.right = below;
        (Some(n), above)
    } else {
        let (below, above) = split(m.left.take(), key);
        m.left = above;
        (below, Some(n))
    }
}

/// Takes the node of `key` out of `t`, if there is one.
fn remove(t: &mut Tree, key: &Atom) {
    let Some(mut n) = t.take() else {
        return;
    };
    match key.cmp(&n.key) {
        Ordering::Less => remove(&mut Arc::make_mut(&mut n).left, key),
        Ordering::Greater => remove(&mut Arc::make_mut(&mut n).right, key),
        Ordering::Equal => {
            *t = match Arc::try_unwrap(n) {
                Ok(n) => merge(n.left, n.right),
                Err(n) => merge(n.left.clone(), n.right.clone()),
            };
            return;
        }
    }
    *t = Some(n);
}

/// The nodes of `a` and of `b`, every pivot of `a` below every pivot of `b`.
fn merge(a: Tree, b: Tree) -> Tree {
    match (a, b) {
        (None, t) | (t, None) => t,
        (Some(mut x), Some(mut y)) => {
            if rank(&x) > rank(&y) {
                let m = Arc::make_mut(&mut x);
                m.right = merge(m.right.take(), Some(y));
                Some(x)
            } else {
                let m = Arc::make_mut(&mut y);
                m.left = merge(Some(x), m.left.take());
                Some(y)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use zedc_int::int::Int;

    fn key(i: u64) -> Atom {
        Atom::Sym(format!("p{i}").into())
    }

    fn row(v: i64) -> Arc<Lin> {
        Arc::new(Lin {
            terms: BTreeMap::new(),
            constant: Int::from(v),
        })
    }

    /// A small deterministic generator (splitmix64).
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n: u64) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            (z ^ (z >> 31)) % n
        }
    }

    /// The map's rows, and checks that each node is above its children and its pivots are in
    /// order.
    fn model(r: &Rows) -> BTreeMap<Atom, Arc<Lin>> {
        let mut stack: Vec<&Node> = r.root.as_deref().into_iter().collect();
        while let Some(n) = stack.pop() {
            for c in [&n.left, &n.right].into_iter().flatten() {
                assert!(rank(c) < rank(n), "a child above its parent");
                stack.push(c);
            }
            if let Some(l) = n.left.as_deref() {
                assert!(l.key < n.key);
            }
            if let Some(r) = n.right.as_deref() {
                assert!(r.key > n.key);
            }
        }
        let m: BTreeMap<Atom, Arc<Lin>> =
            r.nodes().map(|n| (n.key.clone(), n.val.clone())).collect();
        assert_eq!(m.len(), r.nodes().count(), "a pivot twice");
        assert!(m.keys().all(|k| r.get(k).is_some()));
        m
    }

    /// A change as the diff gives it: the first map's pivot and row, and the second's row, by
    /// their constants.
    type Change = (Option<(Atom, i64)>, Option<i64>);

    fn constant(t: &Lin) -> i64 {
        t.constant.to_i128().expect("small") as i64
    }

    /// The diff of `a` and `b`, checked against the diff of their models.
    fn changes(a: &Rows, b: &Rows) -> Vec<Change> {
        let mut out = Vec::new();
        a.diff(b, |s, t| {
            out.push((
                s.map(|(k, v)| (k.clone(), constant(v))),
                t.map(|v| constant(v)),
            ));
        });
        let (ma, mb) = (model(a), model(b));
        let keys: std::collections::BTreeSet<&Atom> = ma.keys().chain(mb.keys()).collect();
        let expected: Vec<Change> = keys
            .into_iter()
            .map(|k| {
                (
                    ma.get(k).map(|v| (k.clone(), constant(v))),
                    mb.get(k).map(|v| constant(v)),
                )
            })
            .filter(|(x, y)| x.as_ref().map(|(_, v)| *v) != *y)
            .collect();
        assert_eq!(out, expected, "the diff against the models'");
        out
    }

    #[test]
    fn one_set_of_pivots_has_one_shape_whatever_the_order() {
        let mut a = Rows::default();
        let mut b = Rows::default();
        for i in 0..200 {
            a.insert(key(i), row(i as i64));
            b.insert(key(199 - i), row((199 - i) as i64));
        }
        fn shape(t: &Tree) -> String {
            match t {
                None => ".".into(),
                Some(n) => format!("({:?} {} {})", n.key, shape(&n.left), shape(&n.right)),
            }
        }
        assert_eq!(shape(&a.root), shape(&b.root));
        // No node is shared, and every row is equal by value: no change.
        assert!(changes(&a, &b).is_empty());
    }

    #[test]
    fn a_map_and_one_made_from_it_differ_in_the_changed_rows_alone() {
        let mut rnd = Rng(7);
        for round in 0..300 {
            let mut a = Rows::default();
            let size = rnd.below(60);
            for _ in 0..size {
                let k = rnd.below(80);
                a.insert(key(k), row(k as i64));
            }
            let mut b = a.clone();
            for _ in 0..rnd.below(6) {
                let k = rnd.below(90);
                match rnd.below(3) {
                    0 => b.remove(&key(k)),
                    1 => b.insert(key(k), row(round)),
                    _ => {
                        if let Some(v) = b.get_mut(&key(k)) {
                            *v = row(-(k as i64));
                        }
                    }
                }
            }
            changes(&a, &b);
            changes(&b, &a);
            // The first is unchanged by the changes made to its copy.
            assert!(model(&a).iter().all(|(k, v)| a.get(k) == Some(v)));
        }
    }

    #[test]
    fn a_row_set_back_to_an_equal_value_is_no_change() {
        let mut a = Rows::default();
        for i in 0..50 {
            a.insert(key(i), row(i as i64));
        }
        let mut b = a.clone();
        b.insert(key(20), row(20));
        b.remove(&key(30));
        b.insert(key(30), row(30));
        assert!(changes(&a, &b).is_empty());
        b.remove(&key(31));
        assert_eq!(changes(&a, &b), vec![(Some((key(31), 31)), None)]);
        assert_eq!(changes(&b, &a), vec![(None, Some(31))]);
    }

    #[test]
    fn the_empty_map_and_absent_pivots() {
        let mut a = Rows::default();
        assert!(changes(&a, &Rows::default()).is_empty());
        a.remove(&key(3));
        assert!(a.get(&key(3)).is_none());
        assert!(a.get_mut(&key(3)).is_none());
        a.insert(key(3), row(3));
        assert_eq!(a.values().count(), 1);
        assert_eq!(
            changes(&a, &Rows::default()),
            vec![(Some((key(3), 3)), None)]
        );
        a.remove(&key(3));
        assert!(a.root.is_none());
    }
}
