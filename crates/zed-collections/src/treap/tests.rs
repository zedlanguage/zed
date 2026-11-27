//! The treap against a `BTreeMap` under random operations, one shape for one set of keys, a
//! summary kept through every operation, and a large treap dropped on a small stack.

use super::*;
use std::collections::BTreeMap;

/// An entry of a key and a value whose priority is a fixed mix of the key, so the tests do not
/// depend on the run's draw; its summary is the sum of the values of its subtree.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct E(u64, u64);

impl Item for E {
    type Key = u64;
    type Sum = u64;
    fn key(&self) -> &u64 {
        &self.0
    }
    fn priority(&self) -> u64 {
        zed_hash::mix(self.0)
    }
    fn sum(&self, left: Option<&u64>, right: Option<&u64>) -> u64 {
        self.1 + left.copied().unwrap_or(0) + right.copied().unwrap_or(0)
    }
}

/// The entries in order, by a walk with a stack.
fn entries(t: &Tree<E>) -> Vec<(u64, u64)> {
    let (mut out, mut stack, mut at) = (Vec::new(), Vec::new(), t.as_deref());
    loop {
        while let Some(n) = at {
            stack.push(n);
            at = n.left.as_deref();
        }
        let Some(n) = stack.pop() else { return out };
        out.push((n.item.0, n.item.1));
        at = n.right.as_deref();
    }
}

/// Whether every node's size and summary are its subtree's and the heap order by priority holds.
fn sound(t: &Tree<E>) -> bool {
    let sum = |t: &Tree<E>| t.as_ref().map_or(0, |n| n.sum);
    let mut stack: Vec<&Node<E>> = t.as_deref().into_iter().collect();
    while let Some(n) = stack.pop() {
        if n.len != 1 + len(&n.left) + len(&n.right)
            || n.sum != n.item.1 + sum(&n.left) + sum(&n.right)
        {
            return false;
        }
        for c in [n.left.as_deref(), n.right.as_deref()]
            .into_iter()
            .flatten()
        {
            if above(c, n) {
                return false;
            }
            stack.push(c);
        }
    }
    true
}

#[test]
fn a_treap_agrees_with_an_ordered_map() {
    let mut rng = crate::seed::Rng::new(7);
    let mut next = |m: u64| rng.below_u64(m);
    let mut t: Tree<E> = None;
    let mut m: BTreeMap<u64, u64> = BTreeMap::new();
    let mut versions = Vec::new();
    for step in 0..4000 {
        let k = next(300);
        match next(5) {
            0 | 1 => {
                t = insert(&t, E(k, step));
                m.insert(k, step);
            }
            2 => {
                t = remove(&t, &k);
                m.remove(&k);
            }
            3 => {
                // A split at `k` and the two sides joined again, the key's own node between.
                let (l, mid, r) = split(&t, &k);
                assert_eq!(mid.map(|n| n.item.1), m.get(&k).copied());
                assert!(sound(&l) && sound(&r));
                assert!(entries(&l).iter().all(|e| e.0 < k));
                assert!(entries(&r).iter().all(|e| e.0 > k));
                let mid = mid.map(|n| E(n.item.0, n.item.1));
                t = join(join(l, mid.and_then(|e| insert(&None, e))), r);
            }
            _ => {
                let cut = next(len(&t) as u64 + 2) as usize;
                t = prefix(&t, cut);
                m = m.into_iter().take(cut).collect();
            }
        }
        assert!(sound(&t));
        let want: Vec<(u64, u64)> = m.iter().map(|(a, b)| (*a, *b)).collect();
        assert_eq!(entries(&t), want);
        assert_eq!(iter(&t).map(|e| (e.0, e.1)).collect::<Vec<_>>(), want);
        assert_eq!(len(&t), m.len());
        assert_eq!(get(&t, &k).map(|e| e.1), m.get(&k).copied());
        for (i, (a, _)) in want.iter().enumerate() {
            assert_eq!(place(&t, a), Some(i));
            assert_eq!(nth(&t, i).0, *a);
        }
        if !m.contains_key(&k) {
            assert_eq!(place(&t, &k), None);
        }
        if step % 500 == 0 {
            versions.push((t.clone(), want));
        }
    }
    // The old versions are unchanged by the operations after them.
    for (v, want) in versions {
        assert_eq!(entries(&v), want);
    }
}

#[test]
fn one_set_of_keys_has_one_shape() {
    // Inserted in increasing and in decreasing order, the keys give one tree.
    let keys: Vec<u64> = (0..1000).map(|i| i * 3 + 1).collect();
    let (mut up, mut down) = (None, None);
    for &k in &keys {
        up = insert(&up, E(k, k));
    }
    for &k in keys.iter().rev() {
        down = insert(&down, E(k, k));
    }
    assert!(sound(&up) && sound(&down));
    assert_eq!(entries(&up), entries(&down));
    assert_eq!(up.as_ref().map(|n| n.item), down.as_ref().map(|n| n.item));
}

#[test]
fn union_and_meet_agree_with_ordered_maps() {
    let mut rng = crate::seed::Rng::new(13);
    let mut next = |m: u64| rng.below_u64(m);
    let one = |t: &Tree<E>| t.as_ref().map(Arc::as_ptr);
    for round in 0..300 {
        let span = 1 + next(200);
        let (mut a, mut b) = (BTreeMap::new(), BTreeMap::new());
        for _ in 0..next(2 * span) {
            a.insert(next(span), next(1000));
        }
        for _ in 0..next(2 * span) {
            b.insert(next(span), next(1000) + 1000);
        }
        let made = |m: &BTreeMap<u64, u64>| from_sorted(m.iter().map(|(&k, &v)| E(k, v)).collect());
        let (x, y) = (made(&a), made(&b));
        // One set of keys has one shape, made from sorted items or an item at a time.
        let mut by_one = None;
        for (&k, &v) in a.iter().rev() {
            by_one = insert(&by_one, E(k, v));
        }
        assert_eq!(shape(&x), shape(&by_one), "{round}");
        let (u, m) = (union(&x, &y), meet(&x, &y));
        assert!(sound(&x) && sound(&y) && sound(&u) && sound(&m), "{round}");
        // A key in both keeps the item of the second tree.
        let mut want_u = a.clone();
        want_u.extend(b.iter().map(|(&k, &v)| (k, v)));
        let want_m: Vec<(u64, u64)> = b
            .iter()
            .filter(|(k, _)| a.contains_key(k))
            .map(|(&k, &v)| (k, v))
            .collect();
        assert_eq!(
            entries(&u),
            want_u.into_iter().collect::<Vec<_>>(),
            "{round}"
        );
        assert_eq!(entries(&m), want_m, "{round}");
        assert_eq!(shape(&u), shape(&made(&entries(&u).into_iter().collect())));
        // A tree is its own union and meet, and the empty tree changes nothing in a union.
        assert_eq!(one(&union(&x, &x)), one(&x));
        assert_eq!(one(&meet(&x, &x)), one(&x));
        assert_eq!(one(&union(&x, &None)), one(&x));
        assert_eq!(one(&union(&None, &y)), one(&y));
        assert!(meet(&x, &None).is_none() && meet(&None, &y).is_none());
        // A tree that gains a key shares with the union every subtree the key's path leaves.
        let k = next(span + 1);
        let more = insert(&x, E(k, 7));
        assert_eq!(one(&union(&x, &more)), one(&more), "{round}");
    }
}

/// The tree's shape: its keys in preorder, `None` for each empty child, read by the accessors.
fn shape(t: &Tree<E>) -> Vec<Option<u64>> {
    let (mut out, mut stack) = (Vec::new(), vec![t]);
    while let Some(t) = stack.pop() {
        match t.as_deref() {
            None => out.push(None),
            Some(n) => {
                assert_eq!(n.rank(), (n.item().priority(), &n.item().0));
                assert_eq!(*n.sum(), n.sum);
                out.push(Some(n.item().0));
                stack.push(n.right());
                stack.push(n.left());
            }
        }
    }
    out
}

#[test]
fn the_in_place_operations_give_the_persistent_trees() {
    let mut rng = crate::seed::Rng::new(11);
    let mut next = |m: u64| rng.below_u64(m);
    let (mut p, mut q): (Tree<E>, Tree<E>) = (None, None);
    let mut copies = Vec::new();
    for step in 0..4000 {
        let k = next(300);
        if next(3) == 0 {
            p = remove(&p, &k);
            remove_mut(&mut q, &k);
        } else {
            p = insert(&p, E(k, step));
            insert_mut(&mut q, E(k, step));
        }
        assert!(sound(&q));
        assert_eq!(shape(&q), shape(&p));
        assert_eq!(entries(&q), entries(&p));
        // A copy shares the nodes of `q`, so the changes after it copy them, and it stays as it
        // was.
        if next(8) == 0 {
            copies.push((q.clone(), entries(&q)));
        }
    }
    assert!(copies.len() > 100);
    for (c, want) in copies {
        assert!(sound(&c));
        assert_eq!(entries(&c), want);
    }
}

/// An entry without a summary, for `get_mut`.
#[derive(Clone)]
struct U(u64, u64);

impl Item for U {
    type Key = u64;
    type Sum = ();
    fn key(&self) -> &u64 {
        &self.0
    }
    fn priority(&self) -> u64 {
        zed_hash::mix(self.0)
    }
    fn sum(&self, _: Option<&()>, _: Option<&()>) {}
}

#[test]
fn get_mut_changes_the_item_in_place_and_leaves_copies_alone() {
    let mut t: Tree<U> = None;
    for k in 0..100 {
        insert_mut(&mut t, U(k, k));
    }
    let copy = t.clone();
    for k in (0..100).step_by(3) {
        get_mut(&mut t, &k).expect("a key of the tree").1 = 1000 + k;
    }
    assert!(get_mut(&mut t, &500).is_none());
    for k in 0..100 {
        let want = if k % 3 == 0 { 1000 + k } else { k };
        assert_eq!(get(&t, &k).map(|u| u.1), Some(want));
        assert_eq!(get(&copy, &k).map(|u| u.1), Some(k));
    }
    // A tree no other shares is changed where it is: no node is copied, the root included.
    drop(copy);
    let root = t.as_ref().map(Arc::as_ptr);
    get_mut(&mut t, &50).expect("a key of the tree").1 = 7;
    insert_mut(&mut t, U(51, 8));
    remove_mut(&mut t, &500);
    assert_eq!(t.as_ref().map(Arc::as_ptr), root);
    assert_eq!(get(&t, &50).map(|u| u.1), Some(7));
}

#[test]
fn a_large_treap_is_dropped_on_a_small_stack() {
    // A tree of 100,000 keys, dropped on a thread of 64 KiB of stack. The drop recurses as deep
    // as the tree. With independent priorities a treap is a random binary search tree, whose
    // nodes lie about 2 ln n = 23 levels deep in expectation and whose height is near
    // 4.31 ln n = 50 (Devroye, "A note on the height of binary search trees", J. ACM 1986,
    // doi:10.1145/5925.5930); the stack holds far more levels than that.
    crate::scaling::on_a_stack(1 << 16, || {
        let mut t: Tree<E> = None;
        for k in 0..100_000 {
            t = insert(&t, E(k, k));
        }
        assert_eq!(len(&t), 100_000);
        drop(t);
    });
}

/// An item of a tree moved by lazy shifts: its key, a shift still to add to the keys below it,
/// and a number of its own, which fixes its priority. Its summary is the largest key of its
/// subtree, which depends on the shift: the children's summaries are read under it.
#[derive(Clone, Debug)]
struct Sh {
    key: i64,
    off: i64,
    id: u64,
}

impl Item for Sh {
    type Key = i64;
    type Sum = i64;
    fn key(&self) -> &i64 {
        &self.key
    }
    fn priority(&self) -> u64 {
        zed_hash::mix(self.id)
    }
    fn sum(&self, left: Option<&i64>, right: Option<&i64>) -> i64 {
        let below = left.into_iter().chain(right).map(|s| s + self.off);
        below.fold(self.key, i64::max)
    }
}

struct Shifts;

use lazy::Lazy;

impl Lazy<Sh> for Shifts {
    fn pending(&self, item: &Sh) -> bool {
        item.off != 0
    }
    fn under(&self, parent: &Sh, child: &Sh) -> Sh {
        Sh {
            key: child.key + parent.off,
            off: child.off + parent.off,
            id: child.id,
        }
    }
    fn cleared(&self, item: &Sh) -> Sh {
        Sh { off: 0, ..*item }
    }
}

/// `t` with `d` added to every key: its root's item mapped.
fn shifted(t: &Tree<Sh>, d: i64) -> Tree<Sh> {
    let n = t.as_deref()?;
    let by = Sh {
        key: 0,
        off: d,
        id: 0,
    };
    let item = Shifts.under(&by, &n.item);
    Some(lazy::mapped(n, item))
}

/// The current keys and numbers of `t` in order, the shifts above each node added, and whether
/// each node's size, summary and heap order (by priority, ties by the current key) hold.
fn shifted_entries(t: &Tree<Sh>) -> (Vec<(i64, u64)>, bool) {
    /// The largest current key of `t`, whose items are under the shift `off`, or `None` if a
    /// node is unsound; its entries pushed on `out`.
    fn walk(t: &Tree<Sh>, off: i64, out: &mut Vec<(i64, u64)>) -> Option<i64> {
        let Some(n) = t.as_deref() else {
            return Some(i64::MIN);
        };
        let key = n.item.key + off;
        let below = off + n.item.off;
        let left = walk(&n.left, below, out)?;
        out.push((key, n.item.id));
        let right = walk(&n.right, below, out)?;
        let top = key.max(left).max(right);
        let heap = [&n.left, &n.right]
            .into_iter()
            .flatten()
            .all(|c| (c.prio, c.item.key + below) < (n.prio, key));
        let ok = n.len == 1 + len(&n.left) + len(&n.right) && n.sum + off == top && heap;
        ok.then_some(top)
    }
    let mut out = Vec::new();
    let ok = walk(t, 0, &mut out).is_some();
    (out, ok)
}

/// A version of [`lazy_trees_agree_with_shifted_lists`]: a tree and the list of its keys and
/// ids, sorted by key.
type Version = (Tree<Sh>, Vec<(i64, u64)>);

#[test]
fn lazy_trees_agree_with_shifted_lists() {
    let mut rng = crate::seed::Rng::new(11);
    let mut next = |m: u64| rng.below_u64(m);
    let mut ids = 0u64;
    // Versions of trees and the lists they hold, each sorted by key with distinct keys.
    let mut trees: Vec<Version> = vec![(None, Vec::new())];
    for _ in 0..3000 {
        let i = next(trees.len() as u64) as usize;
        let (t, want) = trees[i].clone();
        let (t, want) = match next(4) {
            0 => {
                // A shift of the whole tree.
                let d = next(41) as i64 - 20;
                let want = want.iter().map(|&(k, id)| (k + d, id)).collect();
                (shifted(&t, d), want)
            }
            1 => {
                // A split, either side kept.
                let k = next(200) as i64 - 100;
                let (a, b) = lazy::split_below(&t, &k, &Shifts);
                let at = want.partition_point(|&(x, _)| x < k);
                match next(2) {
                    0 => (a, want[..at].to_vec()),
                    _ => (b, want[at..].to_vec()),
                }
            }
            2 => {
                // A join with another version, shifted past this one's last key.
                let (u, other) = trees[next(trees.len() as u64) as usize].clone();
                let top = want.last().map_or(0, |&(k, _)| k);
                let bottom = other.first().map_or(0, |&(k, _)| k);
                let d = top - bottom + 1 + next(3) as i64;
                let mut want = want.clone();
                want.extend(other.iter().map(|&(k, id)| (k + d, id)));
                (lazy::join(t, shifted(&u, d), &Shifts), want)
            }
            _ => {
                // A new item past the last key.
                ids += 1;
                let key = want.last().map_or(0, |&(k, _)| k) + 1 + next(3) as i64;
                let one = lazy::single(Sh {
                    key,
                    off: 0,
                    id: ids,
                });
                let mut want = want.clone();
                want.push((key, ids));
                (lazy::join(t, one, &Shifts), want)
            }
        };
        let (got, sound) = shifted_entries(&t);
        assert!(sound, "sizes, summaries and heap order");
        assert_eq!(got, want);
        trees.push((t, want));
        if trees.len() > 40 {
            trees.swap_remove(next(40) as usize);
        }
    }
    // Every version kept still holds its list: no walk changed a node another tree shares.
    for (t, want) in &trees {
        assert_eq!(&shifted_entries(t).0, want);
    }
}

/// An entry of a key and a priority the test chooses, to build paths; its summary is the sum of
/// the keys of its subtree.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct P(u64, u64);

impl Item for P {
    type Key = u64;
    type Sum = u64;
    fn key(&self) -> &u64 {
        &self.0
    }
    fn priority(&self) -> u64 {
        self.1
    }
    fn sum(&self, left: Option<&u64>, right: Option<&u64>) -> u64 {
        self.0 + left.copied().unwrap_or(0) + right.copied().unwrap_or(0)
    }
}

/// The keys of `t` in preorder, `None` for each empty child, by a loop, each node's size, sum and
/// heap order checked.
fn preorder(t: &Tree<P>) -> Vec<Option<u64>> {
    let sum = |t: &Tree<P>| t.as_ref().map_or(0, |n| n.sum);
    let (mut out, mut stack) = (Vec::new(), vec![t]);
    while let Some(t) = stack.pop() {
        let Some(n) = t.as_deref() else {
            out.push(None);
            continue;
        };
        assert_eq!(n.len, 1 + len(&n.left) + len(&n.right));
        assert_eq!(n.sum, n.item.0 + sum(&n.left) + sum(&n.right));
        for c in [n.left.as_deref(), n.right.as_deref()]
            .into_iter()
            .flatten()
        {
            assert!(!above(c, n), "heap order");
        }
        out.push(Some(n.item.0));
        stack.push(&n.right);
        stack.push(&n.left);
    }
    out
}

/// The number of nodes on the search path of `key` in `t`, its own node counted if it is there.
fn depth(t: &Tree<P>, key: u64) -> usize {
    let (mut d, mut at) = (0, t.as_deref());
    while let Some(n) = at {
        d += 1;
        at = match key.cmp(&n.item.0) {
            Ordering::Less => n.left.as_deref(),
            Ordering::Greater => n.right.as_deref(),
            Ordering::Equal => None,
        };
    }
    d
}

/// Drops `t` node by node, so that a path is not dropped by the compiler's drop, a recursion as
/// deep as the path (STACK-treap-drop-depth). A node another tree shares is left to it.
fn dismantle(t: Tree<P>) {
    let mut stack = vec![t];
    while let Some(t) = stack.pop() {
        if let Some(Ok(mut n)) = t.map(Arc::try_unwrap) {
            stack.push(n.left.take());
            stack.push(n.right.take());
        }
    }
}

/// FAIL-treap-inplace-recursion-depth: each in-place operation on paths of 100,000 nodes, in a
/// thread of a 1 MiB stack, which a recursion one call a node of them overflows. Each result is
/// the persistent operation's tree, and a copy taken before is left as it was.
#[test]
fn the_in_place_operations_take_a_path_of_any_depth() {
    std::thread::Builder::new()
        .stack_size(1 << 20)
        .spawn(|| {
            const M: u64 = 100_000;
            // Key 2i of priority 2|i - M| + 2, the middle one's the highest: below the root, the
            // keys under the middle make a path to the right and those above it a path to the
            // left, each of M nodes.
            let prio = |i: u64| {
                if i == M {
                    u64::MAX
                } else {
                    2 * i.abs_diff(M) + 2
                }
            };
            let items: Vec<P> = (0..=2 * M).map(|i| P(2 * i, prio(i))).collect();
            let prios: Vec<u64> = items.iter().map(|p| p.1).collect();
            let mut t: Tree<P> =
                crate::cartesian::build(items, &prios, |_, p, l, r| node(p, p.1, l, r));
            let copy = t.clone();
            let before = preorder(&copy);
            let mut p = t.clone();
            // The root out: its two paths, of equal priorities in turn, joined into one path
            // that zigzags between them, every node of both on the walk.
            let m = M as usize;
            assert_eq!(depth(&t, 2 * M - 2), m + 1);
            remove_mut(&mut t, &(2 * M));
            // Each persistent result replaces `p`, and the old `p` is dismantled: after this
            // first step its path of about 2M nodes is its own, and the compiler's drop of it
            // would be a recursion as deep as the path (STACK-treap-drop-depth).
            let q = remove(&p, &(2 * M));
            dismantle(std::mem::replace(&mut p, q));
            assert_eq!(preorder(&t), preorder(&p));
            // A key just above the old middle one, of a priority between those of keys 0 and
            // 4M - 2: the walk stops at key 4M - 2, the path's third node, and splits the rest
            // of the path, whose keys are on both sides of the new key in turn, every node on
            // the walk.
            assert!(depth(&t, 2 * M + 1) > 2 * m - 2);
            insert_mut(&mut t, P(2 * M + 1, 2 * M + 1));
            let q = insert(&p, P(2 * M + 1, 2 * M + 1));
            dismantle(std::mem::replace(&mut p, q));
            assert_eq!(preorder(&t), preorder(&p));
            // The key at the bottom of the left side's path, then a new key of the lowest
            // priority there: walks of about M nodes down.
            assert!(depth(&t, 2 * M - 2) > m);
            remove_mut(&mut t, &(2 * M - 2));
            let q = remove(&p, &(2 * M - 2));
            dismantle(std::mem::replace(&mut p, q));
            assert_eq!(preorder(&t), preorder(&p));
            insert_mut(&mut t, P(2 * M - 3, 1));
            let q = insert(&p, P(2 * M - 3, 1));
            dismantle(std::mem::replace(&mut p, q));
            let got = preorder(&t);
            assert_eq!(got, preorder(&p));
            assert!(depth(&t, 2 * M - 3) > m);
            assert_eq!(got.iter().flatten().count(), 2 * m + 1);
            assert_eq!(preorder(&copy), before);
            dismantle(p);
            dismantle(t);
            dismantle(copy);
        })
        .expect("a thread")
        .join()
        .expect("no stack overflow and no failed check");
}
