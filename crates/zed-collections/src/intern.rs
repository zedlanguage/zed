//! An interner: dense ids `0, 1, 2, ...` for distinct values, in the order first seen, and the
//! values back by id (DRY-interners, 2026-11-20). The one copy for the workspace: zed-kernel
//! `types.rs` `Chains::intern` and `types/empty/escape.rs` `intern`, zedc-presburger
//! `deep/canon.rs` `Canon::intern` and the table of equal rows of `presburger.rs`, and zedc-zir
//! `canon/mod.rs` `sorted_facets` each wrote out a map from a value to its id beside the vector
//! of values (or read the vector back out of the map).
//!
//! Complexity tradeoff: each value is held twice, as a key of the map and in the vector, so
//! `K` is `Clone`; at the sites above `K` is a reference, a small tuple or a value the sites
//! cloned the same way before. A table of ids hashed by the values in the vector
//! (hashbrown's `HashTable`) holds each value once, but this crate is a dylib that links no
//! hashbrown, and a second copy beside zed-kernel's could make the crates that link both fail
//! to build. Naive: a search of the vector, O(n) a value and O(n^2) in all; here one hash
//! lookup through the entry API, O(1) expected a value, plus one clone for a new value. Two of
//! the copies it replaced hashed a new value twice (a `get`, then an `insert`).

use std::collections::HashMap;
use std::collections::hash_map::{Entry, RandomState};
use std::hash::{BuildHasher, Hash};
use std::ops::Index;

/// Dense ids for distinct values of `K`, hashed by `S`.
#[derive(Clone, Debug)]
pub struct Interner<K, S = RandomState> {
    ids: HashMap<K, usize, S>,
    values: Vec<K>,
}

impl<K, S: Default> Default for Interner<K, S> {
    fn default() -> Self {
        Interner {
            ids: HashMap::default(),
            values: Vec::new(),
        }
    }
}

impl<K: Eq + Hash + Clone, S: BuildHasher> Interner<K, S> {
    /// The id of `k` and whether it is new: the id it was given before, else the next one,
    /// `k` then kept as that id's value.
    pub fn insert(&mut self, k: K) -> (usize, bool) {
        match self.ids.entry(k) {
            Entry::Occupied(e) => (*e.get(), false),
            Entry::Vacant(e) => {
                let id = self.values.len();
                self.values.push(e.key().clone());
                e.insert(id);
                (id, true)
            }
        }
    }

    /// The id of `k`, given now if it had none.
    pub fn intern(&mut self, k: K) -> usize {
        self.insert(k).0
    }

    /// The id of `k`, if it has one.
    pub fn id(&self, k: &K) -> Option<usize> {
        self.ids.get(k).copied()
    }
}

impl<K, S> Interner<K, S> {
    /// The values, by id.
    pub fn values(&self) -> &[K] {
        &self.values
    }

    /// The values, by id, the map dropped.
    pub fn into_values(self) -> Vec<K> {
        self.values
    }

    /// The number of ids given.
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Whether no id was given.
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Every id dropped, the next one given again 0; the memory is kept for reuse.
    pub fn clear(&mut self) {
        self.ids.clear();
        self.values.clear();
    }
}

/// The value of an id; panics for an id not given.
impl<K, S> Index<usize> for Interner<K, S> {
    type Output = K;

    fn index(&self, id: usize) -> &K {
        &self.values[id]
    }
}

#[cfg(test)]
mod tests {
    use super::Interner;
    use crate::seed::Rng;

    /// Ids by a search of the values seen so far: the naive interner every copy must agree with.
    fn by_search(xs: &[u64]) -> (Vec<usize>, Vec<u64>) {
        let mut values: Vec<u64> = Vec::new();
        let ids = xs
            .iter()
            .map(|x| match values.iter().position(|v| v == x) {
                Some(i) => i,
                None => {
                    values.push(*x);
                    values.len() - 1
                }
            })
            .collect();
        (ids, values)
    }

    #[test]
    fn ids_are_dense_in_the_order_first_seen() {
        let mut t: Interner<&str> = Interner::default();
        assert!(t.is_empty());
        assert_eq!(t.insert("b"), (0, true));
        assert_eq!(t.insert("a"), (1, true));
        assert_eq!(t.insert("b"), (0, false));
        assert_eq!(t.intern("c"), 2);
        assert_eq!((t.id(&"a"), t.id(&"d")), (Some(1), None));
        assert_eq!((t.len(), t[0], t[2]), (3, "b", "c"));
        assert_eq!(t.values(), ["b", "a", "c"]);
        let mut u = t.clone();
        assert_eq!(t.into_values(), vec!["b", "a", "c"]);
        u.clear();
        assert!(u.is_empty() && u.id(&"b").is_none());
        assert_eq!(u.intern("c"), 0);
    }

    #[test]
    fn ids_agree_with_a_search_of_the_values_seen() {
        let (mut rng, _) = Rng::fresh("ids_agree_with_a_search_of_the_values_seen");
        for round in 0..200 {
            let n = rng.below(60);
            let range = 1 + rng.below_u64(40);
            let xs: Vec<u64> = (0..n).map(|_| rng.below_u64(range)).collect();
            let mut t: Interner<u64> = Interner::default();
            let ids: Vec<usize> = xs.iter().map(|&x| t.intern(x)).collect();
            let (want_ids, want_values) = by_search(&xs);
            assert_eq!(ids, want_ids, "round {round}: {xs:?}");
            assert_eq!(t.values(), want_values, "round {round}: {xs:?}");
            for (x, id) in xs.iter().zip(&ids) {
                assert_eq!((t[*id], t.id(x)), (*x, Some(*id)), "round {round}");
            }
        }
    }
}
