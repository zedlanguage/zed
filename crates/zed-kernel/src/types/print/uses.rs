//! How the parts of a printed type use the parts that are named by how often a type uses them
//! (step MSG-derive-print-unions). A part such as a union `1 | 2` gets a definition when a type
//! uses it twice or more and is written in full when it uses it once, so the text of a part
//! that holds it depends on the rest of the type. For each such part `c` that a printed part
//! holds, a [`Uses`] map records the one part that refers to it, or that two or more references
//! to it were seen ([`Use::Many`]). The maps of two parts merge into the map of a part that
//! holds both, and the printer keeps one with each part it keeps for later types of a message,
//! so a later type that takes the part again knows its uses without printing it again.
//!
//! A map is a persistent Patricia trie over the parts' numbers, big-endian, as in Okasaki and
//! Gill, "Fast Mergeable Integer Maps", ACM SIGPLAN Workshop on ML, 1998. A map that a merge
//! leaves unchanged is returned as it was, so maps built from one another share their subtrees,
//! and [`conflicts`] skips a subtree the two maps share.

use std::rc::Rc;

/// The uses of one part.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Use {
    /// One reference, from the part numbered `from`; `named` when the print that made the map
    /// named the part all the same, for its uses outside the part the map belongs to.
    One { from: u32, named: bool },
    /// Two or more references: the part is named in every type that holds them.
    Many,
}

impl Use {
    fn merge(self, other: Use) -> Use {
        match (self, other) {
            (Use::One { from: a, named: x }, Use::One { from: b, named: y }) if a == b => {
                Use::One {
                    from: a,
                    named: x || y,
                }
            }
            _ => Use::Many,
        }
    }
}

/// What a subtree holds, so that a search skips one that holds nothing it looks for.
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
struct Holds {
    one: bool,
    many: bool,
    named_one: bool,
}

impl Holds {
    fn of(u: Use) -> Holds {
        match u {
            Use::One { named, .. } => Holds {
                one: true,
                many: false,
                named_one: named,
            },
            Use::Many => Holds {
                one: false,
                many: true,
                named_one: false,
            },
        }
    }

    fn or(self, other: Holds) -> Holds {
        Holds {
            one: self.one || other.one,
            many: self.many || other.many,
            named_one: self.named_one || other.named_one,
        }
    }
}

#[derive(Debug)]
enum Trie {
    Leaf(u32, Use),
    /// The keys that agree with `prefix` above the bit `bit`, those with the bit clear on the
    /// left.
    Branch {
        prefix: u32,
        bit: u32,
        left: Rc<Trie>,
        right: Rc<Trie>,
        holds: Holds,
    },
}

impl Trie {
    fn holds(&self) -> Holds {
        match self {
            Trie::Leaf(_, u) => Holds::of(*u),
            Trie::Branch { holds, .. } => *holds,
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

/// The uses of the named-by-count parts a printed part holds, by their numbers.
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
    let holds = left.holds().or(right.holds());
    Rc::new(Trie::Branch {
        prefix,
        bit,
        left,
        right,
        holds,
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

/// Whether some key has one use in `p` and many in `z`.
fn conflicts(p: &Rc<Trie>, z: &Rc<Trie>) -> bool {
    if Rc::ptr_eq(p, z) || !p.holds().one || !z.holds().many {
        return false;
    }
    match (&**p, &**z) {
        (Trie::Leaf(k, Use::One { .. }), _) => get(z, *k) == Some(Use::Many),
        (Trie::Leaf(..), _) => false,
        (_, Trie::Leaf(k, _)) => matches!(get(p, *k), Some(Use::One { .. })),
        (
            Trie::Branch {
                prefix: pp,
                bit: mp,
                left: lp,
                right: rp,
                ..
            },
            Trie::Branch {
                prefix: pz,
                bit: mz,
                left: lz,
                right: rz,
                ..
            },
        ) => {
            if mp > mz {
                match (mask(*pz, *mp) == *pp, pz & mp == 0) {
                    (false, _) => false,
                    (true, true) => conflicts(lp, z),
                    (true, false) => conflicts(rp, z),
                }
            } else if mz > mp {
                match (mask(*pp, *mz) == *pz, pp & mz == 0) {
                    (false, _) => false,
                    (true, true) => conflicts(p, lz),
                    (true, false) => conflicts(p, rz),
                }
            } else {
                pp == pz && (conflicts(lp, lz) || conflicts(rp, rz))
            }
        }
    }
}

// Complexity tradeoff: a map of the parts by their numbers in a hash table would take each
// use in O(1), but merging the maps of the parts of a type copies them, O(n) per part and
// O(n²) for a chain of n parts each holding the one before. The trie is persistent: inserting
// a use builds the O(32) nodes on its key's path and shares the rest, a union of a map with
// one of k keys costs O(32 k) and nothing for a subtree the two share, and so does a search
// for a conflict ([`Uses::conflicts`]).
// This is option (2) of COMPLEXITY.md row K110, chosen here without the cross-review the plan
// row asked for (the brief left the method open): keep a part with the uses of each union
// inside it in a shared or persistent map. Option (1), naming a union by its uses in the whole
// message, would be cheaper (no map) but changes the DESIGN rule that a part used once is
// written where it stands, so it needs the author. Measured, rejecting a chain of
// n names each holding a union (`l01_29_diagnostics::type_size`), n = 40 to 320: 7.6 times the
// work and 6.3 times the bytes, where the printer without these maps allocated 43.7 times the
// bytes; with a union of its own at each link 7.8 and 7.9 times (35.5 without).
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
    pub(super) fn get(&self, key: u32) -> Option<Use> {
        get(self.0.as_deref()?, key)
    }

    /// Whether some part used once here was named in the print that made the map: a part
    /// that holds it is written so only where it stands in that type.
    pub(super) fn named_once(&self) -> bool {
        self.0.as_ref().is_some_and(|t| t.holds().named_one)
    }

    /// Whether some part used once here is used twice or more in `all`: a part that holds it
    /// writes it in full, where a type with the uses of `all` names it.
    pub(super) fn conflicts(&self, all: &Uses) -> bool {
        match (&self.0, &all.0) {
            (Some(p), Some(z)) => conflicts(p, z),
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Use, Uses};

    fn one(from: u32) -> Use {
        Use::One { from, named: false }
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
    fn a_conflict_is_a_key_used_once_in_one_map_and_many_times_in_the_other() {
        let p = Uses::default().with(3, one(1)).with(u32::MAX, one(2));
        let z = p.with(3, one(4));
        assert!(p.conflicts(&z));
        assert!(!z.conflicts(&p));
        let q = Uses::default().with(u32::MAX, one(2)).with(8, Use::Many);
        assert!(!q.conflicts(&q.with(8, one(1))));
        assert!(!p.conflicts(&p));
    }

    #[test]
    fn a_part_named_for_uses_outside_it_is_found() {
        let p = Uses::default().with(
            2,
            Use::One {
                from: 1,
                named: true,
            },
        );
        assert!(p.named_once());
        assert!(!p.with(2, one(4)).named_once());
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
        assert!(u.conflicts(&twice));
    }
}
