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
fn an_insertion_leaves_every_set_sharing_its_nodes_as_it_was() {
    // `insert` changes in place the nodes a set alone holds and copies the shared ones: each
    // copy taken before an insertion, sharing all or part of the set, keeps its keys and the
    // counts of every node.
    let mut g = Rng::new(11);
    let mut t: TreapSet<i64> = TreapSet::new();
    let mut want = BTreeSet::new();
    let mut copies: Vec<(TreapSet<i64>, Vec<i64>)> = Vec::new();
    for i in 0..3000 {
        let k = g.int(0, 4_999);
        assert_eq!(t.insert(k), want.insert(k), "insert {k}");
        if i % 97 == 0 {
            copies.push((t.clone(), want.iter().copied().collect()));
        }
    }
    assert_eq!(checked(&t), want.into_iter().collect::<Vec<_>>());
    for (c, keys) in &copies {
        assert_eq!(&checked(c), keys);
    }
    // A key under the root of a set no other holds: the root is changed in place.
    let mut u: TreapSet<i64> = (0..100).collect();
    let root = Arc::as_ptr(u.root.as_ref().unwrap());
    let low = (100..10_000)
        .find(|k| k.priority() < u.root.as_ref().unwrap().prio)
        .unwrap();
    assert!(u.insert(low));
    assert_eq!(Arc::as_ptr(u.root.as_ref().unwrap()), root);
    assert_eq!(checked(&u), (0..100).chain([low]).collect::<Vec<_>>());
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

#[test]
fn is_subset_agrees_on_sets_made_from_one_set() {
    // Two sets edited apart from one set by removals, insertions and cuts, so the walk of
    // `is_subset` meets shared subtrees, roots of one key and both orders of the two roots
    // (steps 3 to 6 of its proof), each way round.
    let mut g = Rng::new(13);
    for round in 0..400 {
        let base = random(&mut g, 300, 600);
        let s = of(&base);
        let mut two = [(s.clone(), base.clone()), (s, base)];
        for _ in 0..g.below(8) {
            let (t, bt) = &mut two[g.below(2)];
            let c = g.int(0, 599);
            match g.below(4) {
                0 => assert_eq!(t.insert(c), bt.insert(c)),
                1 => assert_eq!(t.remove(&c), bt.remove(&c)),
                2 => {
                    *t = t.at_least(&c);
                    *bt = bt.range(c..).copied().collect();
                }
                _ => {
                    *t = t.at_most(&c);
                    *bt = bt.range(..=c).copied().collect();
                }
            }
        }
        let [(a, ba), (b, bb)] = &two;
        assert_eq!(a.is_subset(b), ba.is_subset(bb), "round {round}");
        assert_eq!(b.is_subset(a), bb.is_subset(ba), "round {round}");
        assert!(a.is_subset(a) && a.is_subset(&a.clone()));
    }
}

/// The height of a tree: the nodes on its longest path from the root.
fn height(t: &Tree<i64>) -> u64 {
    t.as_ref()
        .map_or(0, |n| 1 + height(&n.left).max(height(&n.right)))
}

#[test]
fn is_subset_work_within_its_bound() {
    // The proof at `is_subset` (steps 9, 10 and 12 to 14) bounds its work, as `IS_SUBSET_WORK`
    // counts it, by `2U + 2D + 3gh + 1`: at most `2 (U + D) + 1` pairs, and for each of the `g`
    // gaps at most `2h` moves in the two chains of pairs that hold an end of the gap and `h`
    // moves of the first pair inside the gap that moves. Here `D` is bounded by the keys of
    // `other` not in `self`. The input makes the walk without steps 12 to 14 go past that bound:
    // `self` is 1024 keys `2^30` apart and `other` is `self` with 200 keys put into each of 32
    // gaps, chosen so that each is an ancestor of the gap's least end `s` in `other` (a key `z`
    // above `s` is one when it stands above every key from `s` to `z`, so the keys are taken
    // going up from `s` with priorities rising in steps of at most a band). Each of the 200
    // keys then takes step 6 with a pair inside the gap, which without step 12 walks down the
    // search path of the gap in `self` again: about 200 such walks a gap where the bound allows
    // 2 · 200 + 3h units. Priorities are drawn once per run, so the keys are chosen at run time.
    const W: i64 = 1 << 30;
    const KEYS_IN_GAP: u64 = 200;
    let ends: Vec<i64> = (0..1024).map(|j| j * W).collect();
    let small: TreapSet<i64> = ends.iter().copied().collect();
    let mut big_keys = ends.clone();
    let mut gaps = 0;
    for &s in &ends[..1023] {
        if gaps == 32 {
            break;
        }
        // Only an end in the lower half of the priorities, so the band below `u64::MAX` holds
        // the 200 rises.
        let mut last = s.priority();
        if last > u64::MAX / 2 {
            continue;
        }
        let band = (u64::MAX - last) / (2 * KEYS_IN_GAP);
        let mut x = s;
        for _ in 0..KEYS_IN_GAP {
            loop {
                x += 1;
                assert!(x < s + W, "the gap after {s} ran out of keys");
                let p = x.priority();
                if p > last && p - last <= band {
                    last = p;
                    big_keys.push(x);
                    break;
                }
            }
        }
        gaps += 1;
    }
    assert_eq!(gaps, 32);
    let big: TreapSet<i64> = big_keys.iter().copied().collect();
    let u = small.len() as u64; // built apart: no node shared
    let d = (big.len() - small.len()) as u64;
    let h = height(&small.root);
    let bound = 2 * u + 2 * d + 3 * gaps * h + 1;
    IS_SUBSET_WORK.with(|c| c.set(0));
    assert!(small.is_subset(&big));
    let work = IS_SUBSET_WORK.with(|c| c.get());
    eprintln!("is_subset work {work}, bound {bound} (U = {u}, D <= {d}, g = {gaps}, h = {h})");
    assert!(
        work <= bound,
        "is_subset did {work} units of work, over the bound 2U + 2D + 4gh + 1 = {bound}"
    );
}

/// [`HashConsTable`] (TYPE-hashcons): two equal sets made apart, the keys put in up and down,
/// become one tree, still the set of their keys; a set with one key more stays apart; an empty
/// set is left as it is; and the table keeps no set alive, so once both are dropped an equal
/// set made later keeps its own tree, held by it alone. Negative control: without the table,
/// the two equal sets are two trees.
#[test]
fn equal_sets_made_apart_become_one_tree() {
    let set = |keys: &mut dyn Iterator<Item = i64>| {
        let mut s = TreapSet::new();
        keys.for_each(|k| {
            s.insert(k);
        });
        s
    };
    let mut up = set(&mut (0..1000));
    let mut down = set(&mut (0..1000).rev());
    let mut more = set(&mut (0..1001));
    assert!(!up.ptr_eq(&down), "the control: two trees before the table");
    let mut table = HashConsTable::default();
    for s in [&mut up, &mut down, &mut more] {
        table.share(s);
    }
    assert!(up.ptr_eq(&down));
    assert!(!up.ptr_eq(&more));
    assert_eq!(checked(&down), (0..1000).collect::<Vec<_>>());
    let mut empty = TreapSet::new();
    table.share(&mut empty);
    assert!(empty.is_empty());
    drop((up, down));
    let mut later = set(&mut (0..1000));
    table.share(&mut later);
    assert_eq!(Arc::strong_count(later.root.as_ref().unwrap()), 1);
}
