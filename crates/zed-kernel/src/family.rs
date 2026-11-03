//! Families: finite keyed trees, the values the Tier-1 calculus computes over.
//!
//! A family maps each key of one level to a value; a value that is itself a family is the
//! next level down. A *leaf* is a non-family value, and its *keypath* is the sequence of keys
//! that reaches it (sec:keypaths). Two rules of (sec:values_morphisms) hold by construction:
//! every keypath has exactly one writer, and an outer key over an empty level has no keypath,
//! so it is dropped.

use std::cell::Cell;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::btree_map::Entry;
use std::mem;
use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};

use imbl::OrdMap;
use imbl::ordmap::Iter;
use imbl::shared_ptr::DefaultSharedPtr;

use crate::deep::{self, Part};
use crate::error::KernelError;
use crate::value::Value;

/// The keys from a family's top level down to one of its leaves.
pub type Keypath = Vec<Value>;

/// The number that names one family, sequence ([`crate::Items`]) or list of field names
/// ([`crate::value::Fields`]) as it was built, so that provenance can find a family's failures
/// from those of the family it was made from, and a walk can know a shared part met again.
/// Copies share it; a family changed in place takes a new one. Ids are drawn once each and
/// never reused, and a walk only tests them for equality: what it finds does not depend on
/// their values. The empty family, sequence and list have id 0.
pub(crate) type Id = u64;

/// The ids a thread draws from, a block at a time, so that threads building values do not
/// share one counter.
const BLOCK: Id = 1 << 16;
static BLOCKS: AtomicU64 = AtomicU64::new(1);
thread_local! {
    /// The next id of this thread's block, and the end of the block.
    static NEXT: Cell<(Id, Id)> = const { Cell::new((0, 0)) };
}

/// A new id. Block 0 is never drawn, so nothing built non-empty has id 0.
pub(crate) fn fresh_id() -> Id {
    NEXT.with(|next| {
        let (mut id, mut end) = next.get();
        if id == end {
            id = BLOCKS.fetch_add(1, AtomicOrdering::Relaxed) * BLOCK;
            end = id + BLOCK;
        }
        next.set((id + 1, end));
        id
    })
}

/// A finite family. No level of a family is empty except a whole family that has no entries.
/// Its entries sit in a persistent map: a copy of a family costs O(1) whatever its size, and
/// a family one entry larger than another shares all but O(log n) of its nodes with it.
///
/// The second field is the family's [`Id`]: a copy keeps it, and a change takes a new one, so
/// the map is never changed in place except through [`Family::extend`]. The third is the id of
/// the family this one was made from by adding entries to a copy of its map, 0 for none: the
/// two share all but the nodes the change copied, which provenance reads (`Provenance::origins`).
#[derive(Clone, Default)]
pub struct Family(pub(crate) OrdMap<Value, Value>, Id, Id);

impl Drop for Family {
    fn drop(&mut self) {
        if !self.0.is_empty() {
            deep::free(Part::Map(mem::take(&mut self.0)));
        }
    }
}

impl PartialEq for Family {
    fn eq(&self, other: &Self) -> bool {
        deep::families_eq(self, other)
    }
}

impl Eq for Family {}

impl Ord for Family {
    fn cmp(&self, other: &Self) -> Ordering {
        deep::families_cmp(self, other)
    }
}

impl PartialOrd for Family {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// An entry of a level being built. A leaf may hold a whole family, shared, until a leaf beneath
/// it is added, when its top level is expanded into a level of its own.
enum Slot {
    Leaf(Value),
    /// The index of the level beneath.
    Inner(usize),
}

/// The levels of a family being built, the top one first. A level beneath another is always
/// added after it, so a deep keypath needs no recursion to walk or to finish.
struct Levels(Vec<BTreeMap<Value, Slot>>);

impl Levels {
    /// The level beneath `key` of level `at`, added if there is none, a leaf holding a family
    /// expanded. `None` when a leaf is there.
    fn descend(&mut self, at: usize, key: Value) -> Option<usize> {
        let next = self.0.len();
        let slot = self.0[at].entry(key).or_insert(Slot::Inner(next));
        let level = match &*slot {
            Slot::Inner(i) if *i == next => BTreeMap::new(),
            Slot::Inner(i) => return Some(*i),
            Slot::Leaf(Value::Family(f)) => f
                .iter()
                .map(|(k, v)| (k.clone(), Slot::Leaf(v.clone())))
                .collect(),
            Slot::Leaf(_) => return None,
        };
        *slot = Slot::Inner(next);
        self.0.push(level);
        Some(next)
    }

    /// Puts the nonempty family `sub` at `path` as one shared leaf, and returns true, when no
    /// leaf is at `path` and none above it. Otherwise returns false, having added only levels
    /// that the leaves of `sub` would add.
    fn place(&mut self, path: &[Value], sub: &Family) -> bool {
        let (last, above) = path.split_last().expect("keypaths are nonempty");
        let mut at = 0;
        for key in above {
            match self.descend(at, key.key()) {
                Some(next) => at = next,
                None => return false,
            }
        }
        match self.0[at].entry(last.key()) {
            Entry::Occupied(_) => false,
            Entry::Vacant(slot) => {
                slot.insert(Slot::Leaf(Value::Family(sub.clone())));
                true
            }
        }
    }

    /// Adds `leaf` at `path`, which `path` reports if it collides.
    fn insert(&mut self, path: &[Value], leaf: Value) -> Result<(), KernelError> {
        let collision = || KernelError::Collision {
            keypath: path.to_vec(),
        };
        let (last, above) = path.split_last().expect("keypaths are nonempty");
        let mut at = 0;
        for key in above {
            at = self.descend(at, key.key()).ok_or_else(collision)?;
        }
        match self.0[at].entry(last.key()) {
            Entry::Occupied(_) => Err(collision()),
            Entry::Vacant(slot) => {
                slot.insert(Slot::Leaf(leaf));
                Ok(())
            }
        }
    }

    /// The family, each level built after the levels beneath it.
    fn into_family(self) -> Family {
        let mut built = Vec::new();
        built.resize_with(self.0.len(), Family::new);
        for (i, level) in self.0.into_iter().enumerate().rev() {
            let entries = level.into_iter().map(|(k, slot)| match slot {
                Slot::Leaf(v) => (k, v),
                Slot::Inner(j) => (k, Value::Family(mem::take(&mut built[j]))),
            });
            let family = Family::from_map(entries.collect());
            built[i] = family;
        }
        built.swap_remove(0)
    }
}

impl Family {
    /// The family with no entries.
    pub fn new() -> Self {
        Family::default()
    }

    /// The family of the entries `map`, with an id of its own.
    pub(crate) fn from_map(map: OrdMap<Value, Value>) -> Self {
        Family::made_from(map, 0)
    }

    /// The family of the entries `map`, made by adding entries to a copy of the map of the
    /// family whose id is `from`.
    fn made_from(map: OrdMap<Value, Value>, from: Id) -> Self {
        match map.is_empty() {
            true => Family::default(),
            false => Family(map, fresh_id(), from),
        }
    }

    /// The family's id.
    pub(crate) fn id(&self) -> Id {
        self.1
    }

    /// The id of the family this one was made from, 0 for none.
    pub(crate) fn from(&self) -> Id {
        self.2
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
        Family::from_map(
            keys.into_iter()
                .map(|k| {
                    let k = k.into().key();
                    (k.clone(), k)
                })
                .collect(),
        )
    }

    /// Builds a family from its leaves. A leaf whose value is a family contributes that
    /// family's leaves beneath it, sharing the family when nothing else is written there.
    /// Fails with [`KernelError::Collision`] when two leaves
    /// share a keypath, or one leaf's keypath is a prefix of another's, and with
    /// [`KernelError::EmptyKeypath`] for a leaf with no keys.
    pub fn from_leaves(
        leaves: impl IntoIterator<Item = (Keypath, Value)>,
    ) -> Result<Self, KernelError> {
        let mut levels = Levels(vec![BTreeMap::new()]);
        for (path, value) in leaves {
            if path.is_empty() {
                return Err(KernelError::EmptyKeypath);
            }
            match value {
                Value::Family(sub) if sub.is_empty() || levels.place(&path, &sub) => {}
                Value::Family(sub) => {
                    for (mut sub_path, leaf) in sub.leaves() {
                        let mut whole = path.clone();
                        whole.append(&mut sub_path);
                        levels.insert(&whole, leaf)?;
                    }
                }
                leaf => levels.insert(&path, leaf)?,
            }
        }
        Ok(levels.into_family())
    }

    /// The leaves with their keypaths, in keypath order.
    pub fn leaves(&self) -> Vec<(Keypath, Value)> {
        let mut out = Vec::new();
        let mut prefix = Vec::new();
        let mut level = self.0.iter();
        let mut above = Vec::new();
        loop {
            match level.next() {
                Some((k, Value::Family(sub))) => {
                    prefix.push(k.clone());
                    above.push(mem::replace(&mut level, sub.0.iter()));
                }
                Some((k, leaf)) => {
                    prefix.push(k.clone());
                    out.push((prefix.clone(), leaf.clone()));
                    prefix.pop();
                }
                None => match above.pop() {
                    Some(outer) => {
                        level = outer;
                        prefix.pop();
                    }
                    None => return out,
                },
            }
        }
    }

    /// The value at key `k` of the top level.
    pub fn get(&self, k: &Value) -> Option<&Value> {
        // Copied only when it holds a `-0.0`, which its key does not.
        match k.is_key() {
            true => self.0.get(k),
            false => self.0.get(&k.key()),
        }
    }

    /// The top-level entries, in key order.
    pub fn iter(&self) -> impl Iterator<Item = (&Value, &Value)> {
        self.0.iter()
    }

    /// The top-level keys, in order.
    pub fn keys(&self) -> impl Iterator<Item = &Value> {
        self.0.keys()
    }

    /// The union of two families: the leaves of both, where a keypath both write holds the
    /// same leaf in each. Fails with [`KernelError::Collision`], at the first such keypath in
    /// order, when the leaves differ or one family has a leaf above the other's subtree. It
    /// costs O(m log n) for the smaller size m and the larger n: the larger family's entries
    /// are shared, not copied.
    pub fn union(&self, other: &Family) -> Result<Family, KernelError> {
        union(self, other)
    }

    /// Adds the entries at the top level, sharing all but O(m log n) of the map's nodes with the
    /// family it was cloned from, for m entries.
    pub(crate) fn extend(&mut self, entries: impl IntoIterator<Item = (Value, Value)>) {
        self.0.extend(entries);
        if !self.0.is_empty() {
            self.2 = self.1;
            self.1 = fresh_id();
        }
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

/// One level of a union in progress: the larger family, the smaller family's entries yet to
/// add, and the entries so far.
struct Merging<'a> {
    big: &'a Family,
    left: Iter<'a, Value, Value, DefaultSharedPtr>,
    small_is_b: bool,
    out: OrdMap<Value, Value>,
}

impl<'a> Merging<'a> {
    fn new(a: &'a Family, b: &'a Family) -> Self {
        let small_is_b = a.len() >= b.len();
        let (big, small) = if small_is_b { (a, b) } else { (b, a) };
        Merging {
            big,
            left: small.0.iter(),
            small_is_b,
            out: big.0.clone(),
        }
    }
}

/// The union of `a` and `b`. A collision is reported as building `a`'s leaves and then `b`'s
/// would report it: at `b`'s leaf, or, where `a` has a leaf above a subtree of `b`, at the
/// subtree's first leaf.
fn union(a: &Family, b: &Family) -> Result<Family, KernelError> {
    let mut prefix = Vec::new();
    let mut level = Merging::new(a, b);
    let mut above = Vec::new();
    loop {
        let Some((k, s)) = level.left.next() else {
            let Some(outer) = above.pop() else {
                return Ok(Family::made_from(level.out, level.big.id()));
            };
            let inner = mem::replace(&mut level, outer);
            let key = prefix
                .pop()
                .expect("each level beneath the top has its key");
            level.out.insert(
                key,
                Value::Family(Family::made_from(inner.out, inner.big.id())),
            );
            continue;
        };
        let big = level.big;
        let Some(g) = big.0.get(k) else {
            level.out.insert(k.clone(), s.clone());
            continue;
        };
        let (x, y) = if level.small_is_b { (g, s) } else { (s, g) };
        prefix.push(k.clone());
        match (x, y) {
            (Value::Family(x), Value::Family(y)) => {
                above.push(mem::replace(&mut level, Merging::new(x, y)));
            }
            (Value::Family(_), _) => return Err(collision(&prefix)),
            (_, Value::Family(y)) => {
                let mut sub = y;
                loop {
                    let (k, v) = sub.0.get_min().expect("no level of a family is empty");
                    prefix.push(k.clone());
                    match v {
                        Value::Family(f) => sub = f,
                        _ => return Err(collision(&prefix)),
                    }
                }
            }
            (x, y) if x == y => {
                prefix.pop();
                level.out.insert(k.clone(), x.clone());
            }
            _ => return Err(collision(&prefix)),
        }
    }
}

fn collision(keypath: &Keypath) -> KernelError {
    KernelError::Collision {
        keypath: keypath.clone(),
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
        let t = |z| Value::tuple(vec![Value::str("x"), Value::float(z)]);
        let g = Family::from_leaves([(vec![t(-0.0), neg()], Value::Int(3))]).unwrap();
        assert_eq!(g.to_string(), "{(\"x\", 0.0) -> {0.0 -> 3}}");
        assert_eq!(Family::set([neg(), Value::float(0.0)]).len(), 1);
    }
}
