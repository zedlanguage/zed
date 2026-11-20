//! The treap set against a `BTreeSet` under random operations, the invariants of every node, one
//! shape for one set of keys, the operands given back where a result equals one, and a large set
//! dropped on a small stack.

use super::*;
use crate::seed::Rng;
use std::collections::BTreeSet;

/// Checks every node of `s`: keys in order, heap order by priority with ties broken by key, and
/// the size, sum and classes of each subtree; returns the keys in order. A walk with a stack.
fn checked(s: &TreapSet<i64>) -> Vec<i64> {
    // Post-order: each node's subtree checked after its children's.
    let mut out = Vec::new();
    let mut stack: Vec<(&Node<i64>, bool)> =
        s.root.as_deref().map(|n| (n, false)).into_iter().collect();
    while let Some((n, seen)) = stack.pop() {
        if !seen {
            stack.push((n, true));
            for c in [&n.right, &n.left].into_iter().flatten() {
                assert!(above(n, c), "heap order at {}", n.key);
                stack.push((c, false));
            }
            continue;
        }
        assert_eq!(n.len, 1 + len(&n.left) + len(&n.right), "size at {}", n.key);
        let s = n
            .weight
            .wrapping_add(sum(&n.left))
            .wrapping_add(sum(&n.right));
        assert_eq!(n.sum, s, "sum at {}", n.key);
        assert_eq!(n.weight, n.key.weight(), "weight at {}", n.key);
        assert_eq!(n.prio, n.key.priority(), "priority at {}", n.key);
        assert_eq!(n.classes, 1, "classes at {}", n.key);
        if let Some(l) = n.left.as_deref() {
            assert!(l.key < n.key);
        }
        if let Some(r) = n.right.as_deref() {
            assert!(r.key > n.key);
        }
    }
    out.extend(s.iter().copied());
    assert!(out.windows(2).all(|w| w[0] < w[1]), "keys in order");
    assert_eq!(out.len(), s.len());
    out
}

fn of(keys: &BTreeSet<i64>) -> TreapSet<i64> {
    keys.iter().copied().collect()
}

fn keys(s: &TreapSet<i64>) -> BTreeSet<i64> {
    checked(s).into_iter().collect()
}

/// The keys of a tree in pre-order: its shape.
fn shape(s: &TreapSet<i64>) -> Vec<i64> {
    let (mut out, mut stack) = (Vec::new(), Vec::new());
    stack.extend(s.root.as_deref());
    while let Some(n) = stack.pop() {
        out.push(n.key);
        stack.extend(n.right.as_deref());
        stack.extend(n.left.as_deref());
    }
    out
}

/// A random set of up to `n` keys in `0..range`.
fn random(g: &mut Rng, n: usize, range: i64) -> BTreeSet<i64> {
    let k = g.below(n + 1);
    (0..k).map(|_| g.int(0, range - 1)).collect()
}

#[test]
fn every_operation_agrees_with_a_btree_set() {
    let mut g = Rng::new(7);
    for round in 0..400 {
        let range = [8, 64, 1000][round % 3];
        let (a, b) = (random(&mut g, 60, range), random(&mut g, 60, range));
        let (sa, sb) = (of(&a), of(&b));
        assert_eq!(keys(&sa), a);
        assert_eq!(
            sa.sum(),
            a.iter().fold(0u64, |s, k| s.wrapping_add(k.weight()))
        );
        assert_eq!(sa.first(), a.first());
        assert_eq!(sa.last(), a.last());
        for k in 0..range {
            assert_eq!(sa.contains(&k), a.contains(&k));
        }
        assert_eq!(keys(&sa.union(&sb)), a.union(&b).copied().collect());
        assert_eq!(
            keys(&sa.intersection(&sb)),
            a.intersection(&b).copied().collect()
        );
        assert_eq!(
            keys(&sa.difference(&sb)),
            a.difference(&b).copied().collect()
        );
        assert_eq!(
            keys(&sb.difference(&sa)),
            b.difference(&a).copied().collect()
        );
        assert_eq!(sa.is_subset(&sb), a.is_subset(&b));
        assert_eq!(sa.is_disjoint(&sb), a.is_disjoint(&b));
        assert_eq!(sa == sb, a == b);
        assert_eq!(sa.cmp(&sb), a.cmp(&b));
        let c = g.int(0, range - 1);
        assert_eq!(keys(&sa.at_least(&c)), a.range(c..).copied().collect());
        assert_eq!(keys(&sa.at_most(&c)), a.range(..=c).copied().collect());
        let (lo, hi) = (sa.at_most(&c), sb.at_least(&(c + 1)));
        let joined: BTreeSet<i64> = a.range(..=c).chain(b.range(c + 1..)).copied().collect();
        assert_eq!(keys(&lo.concat(&hi)), joined);
        let (mut m, mut bm) = (sa.clone(), a.clone());
        for _ in 0..20 {
            let k = g.int(0, range - 1);
            match g.below(2) {
                0 => assert_eq!(m.insert(k), bm.insert(k)),
                _ => assert_eq!(m.remove(&k), bm.remove(&k)),
            }
            assert_eq!(keys(&m), bm);
        }
        // The operand is left as it was.
        assert_eq!(keys(&sa), a);
    }
}

#[test]
fn sets_made_from_one_set_agree_with_a_btree_set() {
    // Cuts, set operations and edits of one set, combined again: the operations meet shared
    // subtrees, which the stops of `at_once` and the sizes in `combine` answer.
    let mut g = Rng::new(11);
    for _ in 0..200 {
        let base = random(&mut g, 200, 400);
        let s = of(&base);
        let mut sets: Vec<(TreapSet<i64>, BTreeSet<i64>)> = vec![(s, base)];
        for _ in 0..12 {
            let i = g.below(sets.len());
            let j = g.below(sets.len());
            let c = g.int(0, 399);
            let ((x, bx), (y, by)) = (&sets[i], &sets[j]);
            let made = match g.below(6) {
                0 => (x.at_least(&c), bx.range(c..).copied().collect()),
                1 => (x.at_most(&c), bx.range(..=c).copied().collect()),
                2 => (x.union(y), bx.union(by).copied().collect()),
                3 => (x.intersection(y), bx.intersection(by).copied().collect()),
                4 => (x.difference(y), bx.difference(by).copied().collect()),
                _ => {
                    let (mut x, mut bx) = (x.clone(), bx.clone());
                    x.insert(c);
                    bx.insert(c);
                    (x, bx)
                }
            };
            assert_eq!(keys(&made.0), made.1);
            sets.push(made);
        }
    }
}

#[test]
fn one_set_of_keys_has_one_shape() {
    let mut g = Rng::new(3);
    let ks: Vec<i64> = (0..300).map(|_| g.int(0, 9_999)).collect();
    let forward: TreapSet<i64> = ks.iter().copied().collect();
    let backward: TreapSet<i64> = ks.iter().rev().copied().collect();
    assert_eq!(shape(&forward), shape(&backward));
    // A set made by operations has the shape of the same keys inserted.
    let (lo, hi) = (forward.at_most(&5000), forward.at_least(&5001));
    assert_eq!(shape(&lo.union(&hi)), shape(&forward));
    assert_eq!(shape(&lo.concat(&hi)), shape(&forward));
    let mut less = forward.clone();
    less.remove(&ks[0]);
    let mut again = less.clone();
    again.insert(ks[0]);
    assert_eq!(shape(&again), shape(&forward));
}

#[test]
fn a_result_equal_to_an_operand_is_that_operand() {
    let s: TreapSet<i64> = (0..1000).collect();
    let cut = s.at_least(&400);
    assert!(s.intersection(&cut).ptr_eq(&cut));
    assert!(cut.intersection(&s).ptr_eq(&cut));
    assert!(s.union(&cut).ptr_eq(&s));
    assert!(cut.union(&s).ptr_eq(&s));
    assert!(cut.difference(&s).is_empty());
    assert!(s.difference(&s.at_least(&1000)).ptr_eq(&s));
    // A cut that drops nothing is the set itself.
    assert!(s.at_least(&-5).ptr_eq(&s));
    assert!(s.at_most(&999).ptr_eq(&s));
    // A key already there leaves the set as it was.
    let mut t = s.clone();
    assert!(!t.insert(5));
    assert!(t.ptr_eq(&s));
    assert!(!t.remove(&5000));
    assert!(t.ptr_eq(&s));
}

#[test]
fn a_large_set_is_dropped_on_a_small_stack() {
    let run = || {
        let s: TreapSet<i64> = (0..200_000).collect();
        let half = s.at_least(&100_000);
        assert_eq!(s.intersection(&half).len(), 100_000);
        drop(s);
        drop(half);
    };
    crate::scaling::on_a_stack(64 * 1024, run);
}
