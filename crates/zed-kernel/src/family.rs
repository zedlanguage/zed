//! Families: finite keyed trees, the values the Tier-1 calculus computes over.
//!
//! A family maps each key of one level to a value; a value that is itself a family is the
//! next level down. A *leaf* is a non-family value, and its *keypath* is the sequence of keys
//! that reaches it (sec:keypaths). Two rules of (sec:values_morphisms) hold by construction:
//! every keypath has exactly one writer, and an outer key over an empty level has no keypath,
//! so it is dropped.

use std::collections::BTreeMap;
use std::fmt;
use std::sync::Arc;

use crate::error::KernelError;
use crate::value::Value;

/// The keys from a family's top level down to one of its leaves.
pub type Keypath = Vec<Value>;

/// A finite family. No level of a family is empty except a whole family that has no entries.
/// Its entries are shared, so a copy of a family costs O(1) whatever its size.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Default)]
pub struct Family(Arc<BTreeMap<Value, Value>>);

enum Node {
    Leaf(Value),
    Inner(BTreeMap<Value, Node>),
}

fn into_family(level: BTreeMap<Value, Node>) -> Family {
    Family(Arc::new(
        level
            .into_iter()
            .map(|(k, node)| match node {
                Node::Leaf(v) => (k, v),
                Node::Inner(inner) => (k, Value::Family(into_family(inner))),
            })
            .collect(),
    ))
}

fn insert(
    level: &mut BTreeMap<Value, Node>,
    path: &[Value],
    leaf: Value,
    whole: &[Value],
) -> Result<(), KernelError> {
    let collision = || KernelError::Collision {
        keypath: whole.to_vec(),
    };
    let (key, rest) = path.split_first().expect("keypaths are nonempty");
    let key = &key.key();
    if rest.is_empty() {
        if level.contains_key(key) {
            return Err(collision());
        }
        level.insert(key.clone(), Node::Leaf(leaf));
        return Ok(());
    }
    match level
        .entry(key.clone())
        .or_insert_with(|| Node::Inner(BTreeMap::new()))
    {
        Node::Leaf(_) => Err(collision()),
        Node::Inner(inner) => insert(inner, rest, leaf, whole),
    }
}

impl Family {
    /// The family with no entries.
    pub fn new() -> Self {
        Family::default()
    }

    /// A one-level family written out as a literal. A value that is an empty family drops
    /// its key.
    ///
    /// # Panics
    ///
    /// Panics when a key repeats, since a literal with two writers for one keypath is a
    /// mistake in the code that builds it.
    pub fn of<K: Into<Value>, V: Into<Value>>(entries: impl IntoIterator<Item = (K, V)>) -> Self {
        let leaves = entries.into_iter().map(|(k, v)| (vec![k.into()], v.into()));
        Family::from_leaves(leaves).expect("a family literal repeats a key")
    }

    /// A set: each key maps to itself, as a set leaf does, so a membership lookup yields
    /// the element (sec:kernel, `discard`).
    pub fn set<K: Into<Value>>(keys: impl IntoIterator<Item = K>) -> Self {
        Family(Arc::new(
            keys.into_iter()
                .map(|k| {
                    let k = k.into().key();
                    (k.clone(), k)
                })
                .collect(),
        ))
    }

    /// Builds a family from its leaves. A leaf whose value is a family contributes that
    /// family's leaves beneath it. Fails with [`KernelError::Collision`] when two leaves
    /// share a keypath, or one leaf's keypath is a prefix of another's, and with
    /// [`KernelError::EmptyKeypath`] for a leaf with no keys.
    pub fn from_leaves(
        leaves: impl IntoIterator<Item = (Keypath, Value)>,
    ) -> Result<Self, KernelError> {
        let mut root = BTreeMap::new();
        for (path, value) in leaves {
            if path.is_empty() {
                return Err(KernelError::EmptyKeypath);
            }
            match value {
                Value::Family(sub) => {
                    for (mut sub_path, leaf) in sub.leaves() {
                        let mut whole = path.clone();
                        whole.append(&mut sub_path);
                        insert(&mut root, &whole, leaf, &whole)?;
                    }
                }
                leaf => insert(&mut root, &path, leaf, &path)?,
            }
        }
        Ok(into_family(root))
    }

    /// The leaves with their keypaths, in keypath order.
    pub fn leaves(&self) -> Vec<(Keypath, Value)> {
        let mut out = Vec::new();
        self.collect_leaves(&mut Vec::new(), &mut out);
        out
    }

    fn collect_leaves(&self, prefix: &mut Keypath, out: &mut Vec<(Keypath, Value)>) {
        for (k, v) in self.0.iter() {
            prefix.push(k.clone());
            match v {
                Value::Family(sub) => sub.collect_leaves(prefix, out),
                leaf => out.push((prefix.clone(), leaf.clone())),
            }
            prefix.pop();
        }
    }

    /// The value at key `k` of the top level.
    pub fn get(&self, k: &Value) -> Option<&Value> {
        self.0.get(&k.key())
    }

    /// The top-level entries, in key order.
    pub fn iter(&self) -> impl Iterator<Item = (&Value, &Value)> {
        self.0.iter()
    }

    /// The top-level keys, in order.
    pub fn keys(&self) -> impl Iterator<Item = &Value> {
        self.0.keys()
    }

    /// The number of top-level entries.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Whether the family has no entries.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl fmt::Display for Family {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // A set, each leaf its own key (`k -> k`), is written by its members.
        let set = !self.0.is_empty() && self.0.iter().all(|(k, v)| k == v);
        write!(f, "{{")?;
        for (i, (k, v)) in self.0.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            if set {
                write!(f, "{k}")?;
            } else {
                write!(f, "{k} -> {v}")?;
            }
        }
        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kp(keys: &[&str]) -> Keypath {
        keys.iter().map(|k| Value::str(k)).collect()
    }

    #[test]
    fn leaves_round_trip_in_keypath_order() {
        let leaves = vec![
            (kp(&["b", "x"]), Value::Int(2)),
            (kp(&["a"]), Value::Int(1)),
            (kp(&["b", "y"]), Value::Int(3)),
        ];
        let f = Family::from_leaves(leaves).unwrap();
        assert_eq!(f.to_string(), r#"{"a" -> 1, "b" -> {"x" -> 2, "y" -> 3}}"#);
        assert_eq!(
            f.leaves(),
            vec![
                (kp(&["a"]), Value::Int(1)),
                (kp(&["b", "x"]), Value::Int(2)),
                (kp(&["b", "y"]), Value::Int(3))
            ]
        );
    }

    #[test]
    fn two_writers_for_one_keypath_collide() {
        let err = Family::from_leaves(vec![
            (kp(&["a"]), Value::Int(1)),
            (kp(&["a"]), Value::Int(1)),
        ])
        .unwrap_err();
        assert_eq!(
            err,
            KernelError::Collision {
                keypath: kp(&["a"])
            }
        );
    }

    #[test]
    fn a_leaf_above_a_subtree_collides_in_either_order() {
        let leaf_first = Family::from_leaves(vec![
            (kp(&["a"]), Value::Int(1)),
            (kp(&["a", "b"]), Value::Int(2)),
        ]);
        assert_eq!(
            leaf_first.unwrap_err(),
            KernelError::Collision {
                keypath: kp(&["a", "b"])
            }
        );
        let subtree_first = Family::from_leaves(vec![
            (kp(&["a", "b"]), Value::Int(2)),
            (kp(&["a"]), Value::Int(1)),
        ]);
        assert_eq!(
            subtree_first.unwrap_err(),
            KernelError::Collision {
                keypath: kp(&["a"])
            }
        );
    }

    #[test]
    fn an_empty_keypath_is_rejected() {
        assert_eq!(
            Family::from_leaves(vec![(vec![], Value::Int(1))]).unwrap_err(),
            KernelError::EmptyKeypath
        );
    }

    #[test]
    fn an_empty_inner_level_drops_its_key() {
        let f = Family::of([("a", Value::Int(1)), ("b", Value::Family(Family::new()))]);
        assert_eq!(f.to_string(), r#"{"a" -> 1}"#);
        assert_eq!(f.len(), 1);
        assert!(!f.is_empty());
        assert!(Family::new().is_empty());
    }

    #[test]
    fn a_set_maps_each_key_to_itself() {
        let s = Family::set([3, 1]);
        assert_eq!(s.to_string(), "{1, 3}", "a set is written by its members");
        assert_eq!(s.get(&Value::Int(3)), Some(&Value::Int(3)));
        assert_eq!(
            s.keys().cloned().collect::<Vec<_>>(),
            vec![Value::Int(1), Value::Int(3)]
        );
        assert_eq!(s.iter().count(), 2);
    }

    #[test]
    #[should_panic(expected = "repeats a key")]
    fn a_literal_with_a_repeated_key_panics() {
        Family::of([("a", 1), ("a", 2)]);
    }

    #[test]
    fn the_two_zeros_are_one_key() {
        let neg = || Value::float(-0.0);
        let f = Family::from_leaves([(vec![neg()], Value::Int(1))]).unwrap();
        assert_eq!(f.to_string(), "{0.0 -> 1}", "the key holds 0.0's bits");
        assert_eq!(f.get(&Value::float(0.0)), Some(&Value::Int(1)));
        assert_eq!(f.get(&neg()), Some(&Value::Int(1)));
        let both = [
            (vec![neg()], Value::Int(1)),
            (vec![Value::float(0.0)], Value::Int(2)),
        ];
        assert!(matches!(
            Family::from_leaves(both),
            Err(KernelError::Collision { .. })
        ));
        // At any depth: inside a tuple key, and at an inner level.
        let t = |z| Value::Tuple(vec![Value::str("x"), Value::float(z)]);
        let g = Family::from_leaves([(vec![t(-0.0), neg()], Value::Int(3))]).unwrap();
        assert_eq!(g.to_string(), "{(\"x\", 0.0) -> {0.0 -> 3}}");
        assert_eq!(Family::set([neg(), Value::float(0.0)]).len(), 1);
    }
}
