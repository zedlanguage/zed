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
fn a_large_treap_is_dropped_on_a_small_stack() {
    // A tree of 100,000 keys, dropped on a thread of 64 KiB of stack.
    crate::scaling::on_a_stack(1 << 16, || {
        let mut t: Tree<E> = None;
        for k in 0..100_000 {
            t = insert(&t, E(k, k));
        }
        assert_eq!(len(&t), 100_000);
        drop(t);
    });
}
