//! How the parts of a message's types use the parts that are named by how often they are used
//! (steps MSG-derive-print-unions, MSG-derive-print-union-names). A part such as a union `1 | 2`
//! gets a name from the first step of a message whose type uses it twice or more, and keeps it
//! in every later step ([`super::defs::lift`]). For each such part `c` that a part of the
//! message's table holds, a [`Uses`] map records the one part or text that refers to it, or
//! that two or more references to it were seen ([`Use::Many`]). The maps of two parts merge
//! into the map of a part that holds both, so the map of a part is built once and shared by
//! every step that writes the part.
//!
//! A map is a persistent Patricia trie over the parts' numbers, big-endian, as in Okasaki and
//! Gill, "Fast Mergeable Integer Maps", ACM SIGPLAN Workshop on ML, 1998. A map that a merge
//! leaves unchanged is returned as it was, so maps built from one another share their subtrees,
//! and [`Uses::each_new_many`] skips a subtree it has already seen.

use std::collections::HashSet;
use std::rc::Rc;

/// The uses of one part.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Use {
    /// One reference, from the part or text numbered `from`.
    One { from: u32 },
    /// Two or more references: the part is named in every step from the first that holds them.
    Many,
}

impl Use {
    fn merge(self, other: Use) -> Use {
        match (self, other) {
            (Use::One { from: a }, Use::One { from: b }) if a == b => self,
            _ => Use::Many,
        }
    }
}

#[derive(Debug)]
enum Trie {
    Leaf(u32, Use),
    /// The keys that agree with `prefix` above the bit `bit`, those with the bit clear on the
    /// left; `many` when some key below has [`Use::Many`].
    Branch {
        prefix: u32,
        bit: u32,
        left: Rc<Trie>,
        right: Rc<Trie>,
        many: bool,
    },
}

impl Trie {
    /// Whether some key in the subtree has [`Use::Many`].
    fn many(&self) -> bool {
        match self {
            Trie::Leaf(_, u) => *u == Use::Many,
            Trie::Branch { many, .. } => *many,
        }
    }

    /// The key of a leaf, or the prefix of a branch.
    fn prefix(&self) -> u32 {
        match self {
            Trie::Leaf(k, _) => *k,
            Trie::Branch { prefix, .. } => *prefix,
        }
    }
}

/// The uses of the named-by-count parts a part holds, by their numbers.
#[derive(Clone, Default, Debug)]
pub(super) struct Uses(Option<Rc<Trie>>);

/// `key` with the bit `bit` and every bit below cleared.
fn mask(key: u32, bit: u32) -> u32 {
    key & !(bit | (bit - 1))
}

/// The highest bit in which `a` and `b` differ.
fn branching_bit(a: u32, b: u32) -> u32 {
    1 << (31 - (a ^ b).leading_zeros())
}

fn branch(prefix: u32, bit: u32, left: Rc<Trie>, right: Rc<Trie>) -> Rc<Trie> {
    let many = left.many() || right.many();
    Rc::new(Trie::Branch {
        prefix,
        bit,
        left,
        right,
        many,
    })
}

/// The trie of `a` and `b`, whose keys differ above both their branching bits.
fn join(a: Rc<Trie>, b: Rc<Trie>) -> Rc<Trie> {
    let (pa, pb) = (a.prefix(), b.prefix());
    let bit = branching_bit(pa, pb);
    match pa & bit == 0 {
        true => branch(mask(pa, bit), bit, a, b),
        false => branch(mask(pa, bit), bit, b, a),
    }
}

/// `t` with `left` and `right` as the children of its branch, `t` itself if they are its own.
fn rebuild(t: &Rc<Trie>, left: Rc<Trie>, right: Rc<Trie>) -> Rc<Trie> {
    let Trie::Branch {
        prefix,
        bit,
        left: l,
        right: r,
        ..
    } = &**t
    else {
        unreachable!("rebuilt only at a branch")
    };
    match Rc::ptr_eq(l, &left) && Rc::ptr_eq(r, &right) {
        true => t.clone(),
        false => branch(*prefix, *bit, left, right),
    }
}

/// `t` with `key`'s use merged with `u`.
fn insert(t: &Rc<Trie>, key: u32, u: Use) -> Rc<Trie> {
    match &**t {
        Trie::Leaf(k, v) if *k == key => match v.merge(u) {
            m if m == *v => t.clone(),
            m => Rc::new(Trie::Leaf(key, m)),
        },
        Trie::Leaf(..) => join(t.clone(), Rc::new(Trie::Leaf(key, u))),
        Trie::Branch {
            prefix,
            bit,
            left,
            right,
            ..
        } => match (mask(key, *bit) == *prefix, key & bit == 0) {
            (false, _) => join(t.clone(), Rc::new(Trie::Leaf(key, u))),
            (true, true) => rebuild(t, insert(left, key, u), right.clone()),
            (true, false) => rebuild(t, left.clone(), insert(right, key, u)),
        },
    }
}

/// The union of `a` and `b`, the uses of a key in both merged.
fn union(a: &Rc<Trie>, b: &Rc<Trie>) -> Rc<Trie> {
    if Rc::ptr_eq(a, b) {
        return a.clone();
    }
    match (&**a, &**b) {
        (Trie::Leaf(k, u), _) => {
            // The merge is symmetric, so `b` with `a`'s one key merged in is the union.
            insert(b, *k, *u)
        }
        (_, Trie::Leaf(k, u)) => insert(a, *k, *u),
        (
            Trie::Branch {
                prefix: pa,
                bit: ma,
                left: la,
                right: ra,
                ..
            },
            Trie::Branch {
                prefix: pb,
                bit: mb,
                left: lb,
                right: rb,
                ..
            },
        ) => {
            if ma > mb {
                // `a` branches higher: `b` goes under one of its children, or beside it.
                match (mask(*pb, *ma) == *pa, pb & ma == 0) {
                    (false, _) => join(a.clone(), b.clone()),
                    (true, true) => rebuild(a, union(la, b), ra.clone()),
                    (true, false) => rebuild(a, la.clone(), union(ra, b)),
                }
            } else if mb > ma {
                match (mask(*pa, *mb) == *pb, pa & mb == 0) {
                    (false, _) => join(a.clone(), b.clone()),
                    (true, true) => rebuild(b, union(a, lb), rb.clone()),
                    (true, false) => rebuild(b, lb.clone(), union(a, rb)),
                }
            } else if pa == pb {
                rebuild(a, union(la, lb), union(ra, rb))
            } else {
                join(a.clone(), b.clone())
            }
        }
    }
}

#[cfg(test)]
fn get(t: &Trie, key: u32) -> Option<Use> {
    match t {
        Trie::Leaf(k, u) => (*k == key).then_some(*u),
        Trie::Branch {
            prefix,
            bit,
            left,
            right,
            ..
        } => match (mask(key, *bit) == *prefix, key & bit == 0) {
            (false, _) => None,
            (true, true) => get(left, key),
            (true, false) => get(right, key),
        },
    }
}

/// The trie nodes [`Uses::each_new_many`] has walked, each held so that its address is not
/// given to another node while the set lives.
#[derive(Default)]
pub(super) struct Seen(HashSet<*const Trie>, Vec<Rc<Trie>>);

// Complexity tradeoff: a map of the parts by their numbers in a hash table would take each
// use in O(1), but merging the maps of the parts of a type copies them, O(n) per part and
// O(n²) for a chain of n parts each holding the one before. The trie is persistent: inserting
// a use builds the O(32) nodes on its key's path and shares the rest, and a union of a map with
// one of k keys costs O(32 k) and nothing for a subtree the two share. Finding the keys used
// twice or more in the map of each step of a message walks each trie node once over all the
// steps ([`Uses::each_new_many`]): a subtree a step shares with an earlier one was walked then.
// This is option (1) of COMPLEXITY.md row K110, the one the author chose (2026-11-13): a part is
// named by its uses from the first step that uses it twice, so a part's text no longer depends
// on the type it stands in, and the printer keeps no map of its own (option (2) did).
impl Uses {
    /// The map with `key`'s uses merged with `u`.
    pub(super) fn with(&self, key: u32, u: Use) -> Uses {
        Uses(Some(match &self.0 {
            Some(t) => insert(t, key, u),
            None => Rc::new(Trie::Leaf(key, u)),
        }))
    }

    /// The uses of both maps, merged where both have a key.
    pub(super) fn union(&self, other: &Uses) -> Uses {
        match (&self.0, &other.0) {
            (Some(a), Some(b)) => Uses(Some(union(a, b))),
            (None, _) => other.clone(),
            (_, None) => self.clone(),
        }
    }

    /// The uses of `key`, if the map has it.
    #[cfg(test)]
    pub(super) fn get(&self, key: u32) -> Option<Use> {
        get(self.0.as_deref()?, key)
    }

    /// Calls `f` on each key with [`Use::Many`] in a subtree of the map that `seen` does not
    /// hold, and adds the subtrees walked to `seen`. Over maps that share subtrees, each trie
    /// node is walked once.
    pub(super) fn each_new_many(&self, seen: &mut Seen, f: &mut impl FnMut(u32)) {
        let mut stack: Vec<&Rc<Trie>> = self.0.iter().collect();
        while let Some(t) = stack.pop() {
            if !t.many() || !seen.0.insert(Rc::as_ptr(t)) {
                continue;
            }
            seen.1.push(t.clone());
            match &**t {
                Trie::Leaf(k, _) => f(*k),
                Trie::Branch { left, right, .. } => {
                    stack.push(right);
                    stack.push(left);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Seen, Use, Uses};

    fn one(from: u32) -> Use {
        Use::One { from }
    }

    fn new_many(u: &Uses, seen: &mut Seen) -> Vec<u32> {
        let mut out = Vec::new();
        u.each_new_many(seen, &mut |k| out.push(k));
        out
    }

    #[test]
    fn uses_from_two_parts_are_many_and_from_one_stay_one() {
        let a = Uses::default().with(5, one(1)).with(9, one(1));
        let b = Uses::default().with(5, one(2)).with(7, one(3));
        let u = a.union(&b);
        assert_eq!(u.get(5), Some(Use::Many));
        assert_eq!(u.get(7), Some(one(3)));
        assert_eq!(u.get(9), Some(one(1)));
        assert_eq!(u.get(6), None);
        assert_eq!(a.union(&a).get(5), Some(one(1)));
    }

    #[test]
    fn a_key_used_many_times_is_found_once_over_maps_that_share_it() {
        let a = Uses::default()
            .with(3, one(1))
            .with(3, one(2))
            .with(8, one(1));
        let mut seen = Seen::default();
        assert_eq!(new_many(&a, &mut seen), [3]);
        // A map built on `a` shares the subtree of 3; only 8, now used twice, is new.
        let b = a.with(8, one(4)).with(12, one(4));
        assert_eq!(new_many(&b, &mut seen), [8]);
        assert_eq!(new_many(&b, &mut seen), Vec::<u32>::new());
        // A map built apart is walked whole.
        let c = Uses::default().with(3, Use::Many);
        assert_eq!(new_many(&c, &mut seen), [3]);
    }

    #[test]
    fn many_keys_in_any_order_agree_with_a_list() {
        // Keys spread over all 32 bits, each inserted under a parent by its residue.
        let keys: Vec<u32> = (0..2000u32).map(|i| i.wrapping_mul(2654435761)).collect();
        let mut m = Uses::default();
        let mut halves = (Uses::default(), Uses::default());
        for (n, &k) in keys.iter().enumerate() {
            m = m.with(k, one(k % 3));
            match n % 2 {
                0 => halves.0 = halves.0.with(k, one(k % 3)),
                _ => halves.1 = halves.1.with(k, one(k % 3)),
            }
        }
        let u = halves.0.union(&halves.1);
        for &k in &keys {
            assert_eq!(m.get(k), Some(one(k % 3)));
            assert_eq!(u.get(k), Some(one(k % 3)));
        }
        let twice = u.union(&Uses::default().with(keys[7], one(99)));
        assert_eq!(twice.get(keys[7]), Some(Use::Many));
        assert_eq!(new_many(&twice, &mut Seen::default()), [keys[7]]);
    }
}
