//! The kernel's one hasher, [`Digest`]: the digests of values (module `value`), the maps keyed by
//! ids, digests and types (module `types`, `provenance`), and the maps of the checker's filings
//! of tuples (`zedc_types::ty`). It imports no other module, so `value` and `types` both import
//! it without an import cycle (s_01f_import_graph). It replaces the byte-at-a-time hasher that
//! `types` kept beside it (HASH-one-hasher).

use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasherDefault, Hasher};

/// splitmix64's finalizer on each `u64` in turn, from no seed, so a digest is the same on every
/// run; bytes go in eight at a time, and an integer of any width as one word. SipHash, the
/// standard map's hasher, cost about a quarter of filing a tuple again (TY-row-hash) and an
/// eighth of the restriction of a list of three blocks; a hasher that took bytes one at a time
/// made eight finalizer steps of a `usize`, such as a vector's length, and four of a `u32`.
#[derive(Default)]
pub struct Digest(u64);

impl Hasher for Digest {
    fn write(&mut self, bytes: &[u8]) {
        let (words, rest) = bytes.as_chunks::<8>();
        for w in words {
            self.write_u64(u64::from_le_bytes(*w));
        }
        if !rest.is_empty() {
            let mut w = [0; 8];
            w[..rest.len()].copy_from_slice(rest);
            self.write_u64(u64::from_le_bytes(w));
        }
    }

    // A small integer, such as an enum's discriminant, goes in as one word, not as bytes.
    #[inline]
    fn write_u8(&mut self, x: u8) {
        self.write_u64(u64::from(x));
    }

    #[inline]
    fn write_u16(&mut self, x: u16) {
        self.write_u64(u64::from(x));
    }

    #[inline]
    fn write_u32(&mut self, x: u32) {
        self.write_u64(u64::from(x));
    }

    #[inline]
    fn write_usize(&mut self, x: usize) {
        self.write_u64(x as u64);
    }

    // `#[inline]` here and on the methods above: rustc inlines an unmarked function into other
    // crates only when it calls nothing, and without it the meets of many tuples in `zedc_types`
    // cost 7.95% more instructions (COMPLEXITY.md K100).
    #[inline]
    fn write_u64(&mut self, x: u64) {
        self.0 = step(self.0, x);
    }

    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }
}

/// A map hashed by [`Digest`]. Its keys must be ids, numbers or digests the compiler drew, never
/// a program's text: with no seed, a program could choose keys that collide and make each lookup
/// read the whole table (hash flooding), so a map keyed by names keeps the standard map's seeded
/// hasher. Making one costs nothing; the standard map reads a thread-local seed and SipHash-1-3
/// hashes each key (KERNEL-randomstate-cost).
pub type DigestMap<K, V> = HashMap<K, V, BuildHasherDefault<Digest>>;

/// A set hashed by [`Digest`], with the keys of a [`DigestMap`].
pub type DigestSet<K> = HashSet<K, BuildHasherDefault<Digest>>;

/// The digest `h` with the word `x` added: splitmix64's finalizer of the two, the step of
/// [`Digest`], and the combination of two digests that `value` and `types` build theirs with.
#[inline]
pub(crate) fn step(h: u64, x: u64) -> u64 {
    let mut z = (h.rotate_left(29) ^ x).wrapping_add(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::hash::{BuildHasher, BuildHasherDefault};

    fn of(f: impl FnOnce(&mut Digest)) -> u64 {
        let mut d = Digest::default();
        f(&mut d);
        d.finish()
    }

    /// An integer of any width is one word, and bytes are words of eight, the last padded with
    /// zeros: so the keys of the type tables, such as a group's number with a `u32` place or
    /// with a vector of arguments, cost one step a field and one for the vector's length.
    #[test]
    fn integers_are_one_word_and_bytes_eight_to_a_word() {
        let word = of(|d| d.write_u64(200));
        assert_eq!(of(|d| d.write_u8(200)), word);
        assert_eq!(of(|d| d.write_u16(200)), word);
        assert_eq!(of(|d| d.write_u32(200)), word);
        assert_eq!(of(|d| d.write_usize(200)), word);
        assert_eq!(word, step(0, 200));
        let bytes = [1, 2, 3, 4, 5, 6, 7, 8, 9];
        assert_eq!(
            of(|d| d.write(&bytes)),
            of(|d| {
                d.write_u64(u64::from_le_bytes([1, 2, 3, 4, 5, 6, 7, 8]));
                d.write_u64(9);
            })
        );
        assert_eq!(of(|d| d.write(&[])), 0);
    }
    /// Equal keys hash alike and the hash is the same on every run (no seed); keys of one shape
    /// that differ in one field differ, here over every key of a small range of each shape the
    /// tables use. Keys of two shapes may share a hash, as `(0, 0u32)` and `(0, vec![])` both
    /// write the words 0 and 0, but no table holds keys of two shapes.
    #[test]
    fn equal_keys_hash_alike_and_unequal_ones_apart() {
        use std::collections::HashSet;
        let h = BuildHasherDefault::<Digest>::default();
        let (mut by_u32, mut by_bool, mut by_args) =
            (HashSet::new(), HashSet::new(), HashSet::new());
        for a in 0..64u64 {
            for b in 0..64u32 {
                let key = (a, b);
                assert_eq!(h.hash_one(key), h.hash_one((a, b)));
                assert!(by_u32.insert(h.hash_one(key)), "{key:?}");
            }
            for b in [false, true] {
                assert!(by_bool.insert(h.hash_one((a, b, a))), "{a} {b}");
            }
            let args: Vec<u64> = (0..a).collect();
            assert_eq!(h.hash_one((a, &args)), h.hash_one((a, args.clone())));
            assert!(by_args.insert(h.hash_one((a, args))), "{a}");
        }
        assert_eq!(h.hash_one(7u64), step(0, 7));
    }

    /// A [`DigestMap`] reads no seed: two maps given the same keys in the same order hold them in
    /// one order, as on every run, where two standard maps each draw their own seed.
    #[test]
    fn digest_maps_given_the_same_keys_hold_them_in_one_order() {
        let make = || -> DigestMap<u64, ()> { (0..1000).map(|k| (k * 7919, ())).collect() };
        let order = |m: &DigestMap<u64, ()>| m.keys().copied().collect::<Vec<_>>();
        assert_eq!(order(&make()), order(&make()));
        let set = || -> DigestSet<u64> { (0..1000).map(|k| k * 7919).collect() };
        assert_eq!(
            set().into_iter().collect::<Vec<_>>(),
            set().into_iter().collect::<Vec<_>>()
        );
    }
}
