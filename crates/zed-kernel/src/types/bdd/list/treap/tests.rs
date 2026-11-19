//! The treap against a `BTreeMap` under random operations, one shape for one set of keys, and a
//! large treap dropped on a small stack.

use super::*;
use std::collections::BTreeMap;

/// A key whose priority is a fixed mix of the key, so the tests do not depend on the run's draw.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct K(u64);

impl Keyed for K {
    fn priority(&self) -> u64 {
        let mut x = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        x ^ (x >> 31)
    }
}

/// The entries in order, by a walk with a stack.
fn entries(t: &Tree<K, u64>) -> Vec<(u64, u64)> {
    let (mut out, mut stack, mut at) = (Vec::new(), Vec::new(), t.as_deref());
    loop {
        while let Some(n) = at {
            stack.push(n);
            at = n.left.as_deref();
        }
        let Some(n) = stack.pop() else { return out };
        out.push((n.key.0, n.value));
        at = n.right.as_deref();
    }
}

/// Whether every node's size is its subtree's and the heap order by priority holds.
fn sound(t: &Tree<K, u64>) -> bool {
    let mut stack: Vec<&Node<K, u64>> = t.as_deref().into_iter().collect();
    while let Some(n) = stack.pop() {
        if n.len != 1 + len(&n.left) + len(&n.right) {
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
    let mut t: Tree<K, u64> = None;
    let mut m: BTreeMap<u64, u64> = BTreeMap::new();
    let mut versions = Vec::new();
    for step in 0..4000 {
        let k = next(300);
        match next(4) {
            0 | 1 => {
                t = insert(&t, K(k), step);
                m.insert(k, step);
            }
            2 => {
                t = remove(&t, &K(k));
                m.remove(&k);
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
        assert_eq!(len(&t), m.len());
        assert_eq!(get(&t, &K(k)), m.get(&k));
        for (i, (a, _)) in want.iter().enumerate() {
            assert_eq!(place(&t, &K(*a)), Some(i));
            assert_eq!(nth(&t, i), &K(*a));
        }
        if !m.contains_key(&k) {
            assert_eq!(place(&t, &K(k)), None);
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
        up = insert(&up, K(k), k);
    }
    for &k in keys.iter().rev() {
        down = insert(&down, K(k), k);
    }
    assert!(sound(&up) && sound(&down));
    assert_eq!(entries(&up), entries(&down));
    assert_eq!(up.as_ref().map(|n| n.key), down.as_ref().map(|n| n.key));
}

#[test]
fn a_large_treap_is_dropped_on_a_small_stack() {
    // A tree of 100,000 keys, dropped on a thread of 64 KiB of stack.
    std::thread::Builder::new()
        .stack_size(1 << 16)
        .spawn(|| {
            let mut t: Tree<K, u64> = None;
            for k in 0..100_000 {
                t = insert(&t, K(k), k);
            }
            assert_eq!(len(&t), 100_000);
            drop(t);
        })
        .expect("a thread")
        .join()
        .expect("the treap dropped");
}
