//! The rows of a hull by their pivots, in a persistent treap whose shape depends only on the
//! pivots it holds in a run: each node's priority is drawn once per run from its pivot, ties
//! broken by the pivot's order. A map made from another by a few changes copies the paths to
//! the changed pivots and shares every other subtree with it, and since both have the one shape
//! their keys give, the subtrees they share sit at the same places in both. The difference of
//! the two is found by a walk that passes over a shared subtree at once. The treap is
//! [`zed_collections::treap`] (plan row DRY-persistent-trees-2026-11-26), changed in place.

use std::cmp::Ordering;
use std::fmt;
use std::sync::Arc;

use zed_collections::priority::Priorities;
use zed_collections::treap::{self, Item, Node, Tree};

use super::Form;

/// A row and its pivot: an item of the treap.
struct Row<F: Form> {
    key: F::Atom,
    val: Arc<F>,
}

// Derived, `Clone` would ask `F::Atom: Clone` through `F` alone; written out, it clones the key
// and the shared row.
impl<F: Form> Clone for Row<F> {
    fn clone(&self) -> Self {
        Row {
            key: self.key.clone(),
            val: self.val.clone(),
        }
    }
}

impl<F: Form> Item for Row<F> {
    type Key = F::Atom;
    type Sum = ();
    fn key(&self) -> &F::Atom {
        &self.key
    }
    fn priority(&self) -> u64 {
        prio_of(&self.key)
    }
    fn sum(&self, _: Option<&()>, _: Option<&()>) {}
}

/// The priorities of the pivots, drawn once per run ([`zed_collections::priority`]). Tag 9, as
/// when the rows were in zedc-presburger, so a run draws the same priorities as before.
static PRIORITIES: Priorities = Priorities::new(9);

/// The priority of a pivot: the run's random polynomial of degree 4 at a random polynomial hash
/// of the pivot's `Hash` stream ([`Priorities::hash`]). Distinct pivots have distinct streams
/// and tie with probability at most `(S + 1)/p` a pair for streams of `S` symbols; the
/// priorities are otherwise 5-wise independent and uniform, and every node's depth is
/// `O(log n)` in expectation for every set of pivots (Seidel and Aragon, "Randomized search
/// trees", Algorithmica 16, 1996, doi:10.1007/BF01940876, Theorem 3.3 and section 6; the full
/// comment and the proof are in module
/// [`zed_collections::priority`]), where the fixed hash this replaces had no bound for chosen
/// pivots (COMPLEXITY.md K123). The shape is never shown: [`Rows`] is read and printed in order.
fn prio_of<K: std::hash::Hash>(key: &K) -> u64 {
    PRIORITIES.hash(key)
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
// B-tree copied about log16 n nodes of 16; and two maps that hold equal rows in nodes they do
// not share are compared row by row, which costs their size, as the B-tree's diff did. The
// answers are the same. Tests
// `l01_39_reduced_product::hull::a_join_costs_near_the_rows_that_differ` and
// `a_join_costs_near_the_rows_that_differ_wherever_they_sort`; COMPLEXITY.md S26.
/// The rows of a hull by their pivots.
pub(super) struct Rows<F: Form> {
    root: Tree<Row<F>>,
}

// Written out for the reason given at `Row`'s `Clone`.
impl<F: Form> Clone for Rows<F> {
    fn clone(&self) -> Self {
        Rows {
            root: self.root.clone(),
        }
    }
}

impl<F: Form> Default for Rows<F> {
    fn default() -> Self {
        Rows { root: None }
    }
}

impl<F: Form> Rows<F> {
    /// The row of `key`. O(depth).
    pub(super) fn get(&self, key: &F::Atom) -> Option<&Arc<F>> {
        treap::get(&self.root, key).map(|r| &r.val)
    }

    /// The row of `key`, which the map holds, to change. The nodes on the path to it that the
    /// map shares with another are copied first, also when the key is absent. O(depth).
    pub(super) fn get_mut(&mut self, key: &F::Atom) -> Option<&mut Arc<F>> {
        treap::get_mut(&mut self.root, key).map(|r| &mut r.val)
    }

    /// Puts `val` at `key`, in place of any row there. O(depth) expected.
    pub(super) fn insert(&mut self, key: F::Atom, val: Arc<F>) {
        treap::insert_mut(&mut self.root, Row { key, val });
    }

    /// Takes out the row of `key`, if there is one. O(depth) expected.
    pub(super) fn remove(&mut self, key: &F::Atom) {
        treap::remove_mut(&mut self.root, key);
    }

    /// The rows, in pivot order.
    pub(super) fn values(&self) -> impl Iterator<Item = &Arc<F>> {
        treap::iter(&self.root).map(|r| &r.val)
    }

    /// Calls `f` on each pivot whose row differs between `self` and `other`, in pivot order,
    /// with the pivot and row of `self` and the row of `other`, either absent where that map
    /// has no row there. Rows are compared by value. O((k + 1) · depth) expected, for k
    /// differing rows, when the two maps share their other subtrees.
    pub(super) fn diff<'a>(
        &'a self,
        other: &'a Rows<F>,
        mut f: impl FnMut(Option<(&'a F::Atom, &'a Arc<F>)>, Option<&'a Arc<F>>),
    ) {
        let start = |t: &'a Tree<Row<F>>| t.as_deref().map(Step::Tree).into_iter().collect();
        let (mut a, mut b): (Vec<Step<'a, F>>, Vec<Step<'a, F>>) =
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
                        match x.rank().cmp(&y.rank()) {
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

impl<F: Form> fmt::Debug for Rows<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map()
            .entries(treap::iter(&self.root).map(|r| (&r.key, &r.val)))
            .finish()
    }
}

/// What a diff's walk of one map has still to visit, the next on top: a whole subtree, or one
/// node's row alone (its left subtree visited, its right one below it on the stack).
enum Step<'a, F: Form> {
    Tree(&'a Node<Row<F>>),
    Entry(&'a Row<F>),
}

// Derived, `Clone` and `Copy` would ask them of `F`; a step holds only references.
impl<F: Form> Clone for Step<'_, F> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<F: Form> Copy for Step<'_, F> {}

/// Replaces the subtree on top of `stack` by its left subtree, its root's row and its right
/// subtree, the left on top.
fn open<F: Form>(stack: &mut Vec<Step<'_, F>>) {
    let Some(Step::Tree(n)) = stack.pop() else {
        unreachable!("a subtree on top of the walk");
    };
    stack.extend(n.right().as_deref().map(Step::Tree));
    stack.push(Step::Entry(n.item()));
    stack.extend(n.left().as_deref().map(Step::Tree));
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::super::tests::Lin;
    use super::*;
    use zedc_int::int::Int;

    type Atom = Arc<str>;
    type Rows = super::Rows<Lin>;

    fn key(i: u64) -> Atom {
        format!("p{i}").into()
    }

    fn row(v: i64) -> Arc<Lin> {
        Arc::new(Lin {
            terms: BTreeMap::new(),
            constant: Int::from(v),
        })
    }

    /// The map's rows, and checks that each node is above its children and its pivots are in
    /// order.
    fn model(r: &Rows) -> BTreeMap<Atom, Arc<Lin>> {
        let mut stack: Vec<&Node<Row<Lin>>> = r.root.as_deref().into_iter().collect();
        while let Some(n) = stack.pop() {
            for c in [n.left(), n.right()].into_iter().flatten() {
                assert!(c.rank() < n.rank(), "a child above its parent");
                stack.push(c);
            }
            if let Some(l) = n.left().as_deref() {
                assert!(l.item().key < n.item().key);
            }
            if let Some(r) = n.right().as_deref() {
                assert!(r.item().key > n.item().key);
            }
        }
        let m: BTreeMap<Atom, Arc<Lin>> = treap::iter(&r.root)
            .map(|e| (e.key.clone(), e.val.clone()))
            .collect();
        assert_eq!(m.len(), treap::iter(&r.root).count(), "a pivot twice");
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
        fn shape(t: &Tree<Row<Lin>>) -> String {
            match t {
                None => ".".into(),
                Some(n) => format!(
                    "({:?} {} {})",
                    n.item().key,
                    shape(n.left()),
                    shape(n.right())
                ),
            }
        }
        assert_eq!(shape(&a.root), shape(&b.root));
        // No node is shared, and every row is equal by value: no change.
        assert!(changes(&a, &b).is_empty());
    }

    #[test]
    fn a_map_and_one_made_from_it_differ_in_the_changed_rows_alone() {
        let mut rnd = crate::seed::Rng::new(7);
        for round in 0..300 {
            let mut a = Rows::default();
            let size = rnd.below_u64(60);
            for _ in 0..size {
                let k = rnd.below_u64(80);
                a.insert(key(k), row(k as i64));
            }
            let mut b = a.clone();
            for _ in 0..rnd.below_u64(6) {
                let k = rnd.below_u64(90);
                match rnd.below_u64(3) {
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
