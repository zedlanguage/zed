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
/// read the whole table (hash flooding), so a map keyed by names takes the seeded [`TextState`].
/// Making one costs nothing; the standard map reads a thread-local seed and SipHash-1-3
/// hashes each key (KERNEL-randomstate-cost).
pub type DigestMap<K, V> = HashMap<K, V, BuildHasherDefault<Digest>>;

/// A set hashed by [`Digest`], with the keys of a [`DigestMap`].
pub type DigestSet<K> = HashSet<K, BuildHasherDefault<Digest>>;

/// The [`Digest`] of `x`, the same in every run: for a content hash of ids, numbers or digests.
pub fn digest_hash<T: std::hash::Hash + ?Sized>(x: &T) -> u64 {
    use std::hash::BuildHasher;
    BuildHasherDefault::<Digest>::default().hash_one(x)
}

/// The hasher of a map or set keyed by a program's text, such as names (DRY-sorted-structures,
/// row 3): foldhash's fast hasher (O. Peters, foldhash 0.2, the default of hashbrown), seeded at
/// random (a seed per map beside one global seed drawn at random once per process), so a program
/// cannot choose names that collide (hash flooding needs the seed, which a written program does
/// not see), and a few instructions per 8 bytes of text, where
/// SipHash-1-3 took 43M of the 115M instructions of FAIL-ratio-payload-renamed's facts of 16000.
/// It is not as strong as SipHash against an attacker who watches timings, which a compiler run on
/// a written program does not face. Iteration order changes from run to run, so a map of this
/// hasher must never be iterated where the order reaches a result: look keys up only.
pub type TextState = hashbrown::DefaultHashBuilder;

/// A map keyed by a program's text, hashed by [`TextState`].
pub type TextMap<K, V> = HashMap<K, V, TextState>;

/// A set of keys made of a program's text, hashed by [`TextState`].
pub type TextSet<K> = HashSet<K, TextState>;

/// The one [`TextState`] of the process, seeded at random once: for a hash of text kept and
/// compared after the call that made it, such as a key made of the hash of a system of
/// constraints (`zedc_presburger`'s memos of repairs and its rows by terms), and for a
/// persistent map whose equal contents must hash and iterate alike in one run (`conjuncts`).
/// A [`TextMap`] that only looks keys up draws its own seed instead.
static TEXT: std::sync::LazyLock<TextState> = std::sync::LazyLock::new(TextState::default);

/// A copy of the process's one [`TextState`] (see `TEXT`).
pub fn text_state() -> TextState {
    TEXT.clone()
}

/// The hash of the text `x` by the process's one [`TextState`]: the same for equal `x` all
/// through one run, not chosen by the program (hash flooding needs the seed), and different
/// from run to run, so it must decide nothing but where a key is kept.
pub fn text_hash<T: std::hash::Hash + ?Sized>(x: &T) -> u64 {
    use std::hash::BuildHasher;
    TEXT.hash_one(x)
}

/// A hasher of the process's one [`TextState`], for a hash of text written piece by piece; its
/// `finish` agrees with [`text_hash`] of the same pieces.
pub fn text_hasher() -> <TextState as std::hash::BuildHasher>::Hasher {
    use std::hash::BuildHasher;
    TEXT.build_hasher()
}

/// The hasher of a content hash that must be the same in every run, such as a digest whose
/// value reaches an order, a number shown to the user, or a test's expected output: the standard
/// library's SipHash-1-3 with both keys zero (`DefaultHasher::new`), so the hash of a value is
/// fixed for one build of the standard library. SipHash-c-d: J.-P. Aumasson and D. J.
/// Bernstein, "SipHash: a fast short-input PRF", INDOCRYPT 2012, LNCS 7668, pp. 489-508,
/// doi:10.1007/978-3-642-34931-7_28 (Crossref and the authors' copy, cr.yp.to, checked
/// 2026-11-20). Section 2: the state is four words `v0..v3` set from the 128-bit key `k0, k1`
/// xored with four constants; each 8-byte word `m` of the input (the last padded with null
/// bytes and "ending with a byte encoding the positive integer b mod 256") is xored into `v3`,
/// then `c` SipRounds of add-rotate-xor, then xored into `v0`; at the end "SipHash-c-d xors the
/// constant ff to the state: v2 ⊕= ff", `d` SipRounds run, and the hash is `v0 ^ v1 ^ v2 ^ v3`.
/// The paper's "fast proposal is thus SipHash-2-4"; the standard library takes `c = 1, d = 3`
/// (its own documentation, from memory, not checked); here the key is `k0 = k1 = 0`, so the
/// hash is a fixed function, not a PRF: it keeps the mixing, not the secret. Test:
/// `the_fixed_and_digest_hashes_are_the_ones_they_replaced` checks it is `DefaultHasher::new`,
/// not that that is SipHash-1-3. It reads a value's bytes as one stream, so a text hashes as its
/// `str` does. A program could choose values that collide, so a map whose keys are a program's
/// text takes [`TextState`]; and SipHash costs several times foldhash's
/// instructions per word, so a hash that need not be fixed takes [`Digest`] or [`text_hash`].
/// The one copy of the `BuildHasherDefault::<DefaultHasher>` the compiler wrote at each such
/// site before (DRY-sorted-structures-2, job 3).
pub type FixedState = BuildHasherDefault<std::hash::DefaultHasher>;

/// The hash of `x` by [`FixedState`]: the same in every run.
pub fn fixed_hash<T: std::hash::Hash + ?Sized>(x: &T) -> u64 {
    use std::hash::BuildHasher;
    FixedState::default().hash_one(x)
}

/// A hasher of [`FixedState`], for a fixed hash written piece by piece; its `finish` agrees with
/// [`fixed_hash`] of the same pieces.
pub fn fixed_hasher() -> std::hash::DefaultHasher {
    std::hash::DefaultHasher::new()
}

/// The digest `h` with the word `x` added: splitmix64's finalizer of the two, the step of
/// [`Digest`], and the combination of two digests that `value` and `types` build theirs with;
/// also the step of `zedc_preimage::address`'s digest of terms (DRY-sorted-structures, row 2).
///
/// The constants are splitmix64's: S. Vigna, `splitmix64.c` (2015, public domain,
/// <https://prng.di.unimi.it/splitmix64.c>), "a fixed-increment version of Java 8's
/// SplittableRandom generator", which is G. L. Steele Jr., D. Lea and C. H. Flood, "Fast
/// splittable pseudorandom number generators", OOPSLA 2014, ACM, pp. 453-472,
/// doi:10.1145/2660193.2660195 (Crossref and Vigna's source checked 2026-11-20; the constants
/// here equal his). The golden-ratio increment `0x9e37_79b9_7f4a_7c15` and the multipliers
/// and shifts 30, 27, 31 of its finalizer, a bijection of `u64` ("xorshifts and
/// multiplications by odd constants are invertible", Vigna) that mixes the input bits into
/// the output bits (an avalanche claim not tested here). The
/// rotation by 29 of `h` before the xor makes the step depend on the order of the words, so
/// `step(step(0, a), b)` and `step(step(0, b), a)` differ; `bdd::set::tests` inverts the step
/// in each argument and relies on these exact constants.
///
/// `tests/src/seed.rs` `mix` is a copy of `step(0, x)`, kept because zed-graph and zedc-solvers
/// compile that file into their tests and do not depend on this crate.
#[inline]
pub fn step(h: u64, x: u64) -> u64 {
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

    /// The process's one text hash: equal text hashes alike in every call, and a copy of the
    /// state and the piecewise hasher agree with it; unequal text of a small range hashes apart.
    #[test]
    fn the_text_hash_is_one_hash_through_the_run() {
        use std::hash::{Hash, Hasher};
        let names: Vec<String> = (0..2000).map(|i| format!("x{i}")).collect();
        let mut seen = HashSet::new();
        for n in &names {
            let h = text_hash(n.as_str());
            assert_eq!(h, text_hash(n.as_str()));
            assert_eq!(h, text_state().hash_one(n.as_str()));
            let mut w = text_hasher();
            n.as_str().hash(&mut w);
            assert_eq!(h, w.finish());
            assert!(seen.insert(h), "{n}");
        }
    }

    /// The fixed hash is the standard library's SipHash-1-3 with zero keys, which the sites it
    /// replaced wrote out (`DefaultHasher::new`), and the piecewise hasher agrees with it; the
    /// digest hash is `Digest`'s. A text hashes as its `str`, in one stream.
    #[test]
    fn the_fixed_and_digest_hashes_are_the_ones_they_replaced() {
        use std::hash::{Hash, Hasher};
        for i in 0..2000u64 {
            let n = format!("x{i}");
            let mut sip = std::hash::DefaultHasher::new();
            (n.as_str(), i).hash(&mut sip);
            let mut w = fixed_hasher();
            (n.as_str(), i).hash(&mut w);
            assert_eq!(fixed_hash(&(n.as_str(), i)), sip.finish());
            assert_eq!(w.finish(), sip.finish());
            let mut d = Digest::default();
            (n.as_str(), i).hash(&mut d);
            assert_eq!(digest_hash(&(n.as_str(), i)), d.finish());
        }
    }
}
