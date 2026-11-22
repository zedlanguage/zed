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
    // cost 7.95% more instructions (COMPLEXITY.md K100). Source: rust-lang/rust PR 116505,
    // "Automatically enable cross-crate inlining for small functions" (Rust 1.75), which infers
    // it "only ... for functions whose optimized_mir does not contain any calls or asserts", and
    // below a size threshold (the PR page read 2026-11-20). `write_u64` calls `step`, so it is
    // such a function only if the MIR inliner removes that call first; the measurement above
    // shows it was not inlined. No test checks the inlining.
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

/// A map keyed by values whose hashes a program can make tie: types, rows and groups, whose
/// `Hash` writes a digest of their contents that a program can solve for (each step of
/// [`step`] is a bijection in either argument; PERF-set-tied-digest-depth). It is hashed by `H`
/// ([`ByHash`], the key's `Hash` by [`Digest`], unless another is named), and the keys of one
/// hash are kept in their order. A key whose hash ties with `b`
/// others then costs `O(log b)` comparisons, where a [`DigestMap`] compares it with all `b`
/// (PERF-row-hash-tied-digest: 4,096 rows of one digest took 8,386,560 comparisons). The keys'
/// `Ord` must agree with their `Eq` and `Hash`: keys equal by order hash alike.
//
// Complexity tradeoff (COMPLEXITY.md K142): the naive map is a `DigestMap`, one hash and one
// comparison per key in the usual case, but `O(b)` comparisons for a key in a bucket of `b`
// tied keys, so `n` keys of one hash cost `n(n-1)/2`. Used: a hashed map of slots, each one key
// or an ordered map of the keys of one hash, `O(log b)` comparisons per key. A slot of one key
// costs what the `DigestMap` does; the ordered map is made only on a tie. Given up: a tie
// allocates an ordered map, and the keys of one hash are compared by `Ord`, which for tied types
// reads their contents (as `Eq` did). Prior work: hashing with ordered buckets is Java 8's
// `HashMap`, which turns a bucket of more than 8 keys into a red-black tree ordered by
// `Comparable` (JEP 180, "Handle Frequent HashMap Collisions with Balanced Trees", 2012).
pub struct TiedMap<K, V, H = ByHash> {
    slots: DigestMap<u64, Slot<K, V>>,
    len: usize,
    hash: std::marker::PhantomData<H>,
}

/// The hash a [`TiedMap`] files a key by: equal for keys equal by `Ord`.
pub trait KeyHash<K> {
    /// The hash of `k`.
    fn hash(k: &K) -> u64;
}

/// A key's `Hash`, by [`Digest`]: a [`TiedMap`]'s hash unless it names another.
pub struct ByHash;

impl<K: std::hash::Hash> KeyHash<K> for ByHash {
    fn hash(k: &K) -> u64 {
        digest_hash(k)
    }
}

/// The keys of one hash in a [`TiedMap`]: one, nearly always, or an ordered map once a second
/// key ties with it.
enum Slot<K, V> {
    One(K, V),
    Many(std::collections::BTreeMap<K, V>),
}

impl<K, V, H> Default for TiedMap<K, V, H> {
    fn default() -> Self {
        TiedMap {
            slots: DigestMap::default(),
            len: 0,
            hash: std::marker::PhantomData,
        }
    }
}

impl<K: Ord, V, H: KeyHash<K>> TiedMap<K, V, H> {
    /// The slot `k` is filed in: its hash by `H` hashed again by the process's seeded
    /// [`text_hash`]. A program can solve for keys whose hashes differ but fall in one probe
    /// sequence of an unseeded table (the flooding of [`DigestMap`]'s rule, KERNEL-bytype-
    /// flooding); with the seed, distinct hashes spread, and equal ones meet in one slot, where
    /// their order tells them apart.
    fn slot(k: &K) -> u64 {
        text_hash(&H::hash(k))
    }

    /// The number of keys.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Whether the map holds no key.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The value of `k`.
    pub fn get(&self, k: &K) -> Option<&V> {
        match self.slots.get(&Self::slot(k))? {
            Slot::One(key, v) => (key == k).then_some(v),
            Slot::Many(m) => m.get(k),
        }
    }

    /// The value of `k`, to change.
    pub fn get_mut(&mut self, k: &K) -> Option<&mut V> {
        match self.slots.get_mut(&Self::slot(k))? {
            Slot::One(key, v) => (&*key == k).then_some(v),
            Slot::Many(m) => m.get_mut(k),
        }
    }

    /// Whether `k` is a key.
    pub fn contains_key(&self, k: &K) -> bool {
        self.get(k).is_some()
    }

    /// Puts `v` at `k`, giving back the value that was there.
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        let mut v = Some(v);
        let old = self.at(k, &mut || v.take().expect("one value"));
        // `v` is still there when `k` was a key, and then it replaces that key's value.
        let new = v?;
        Some(std::mem::replace(old, new))
    }

    /// The value of `k`, put there by `f` when `k` is not a key.
    pub fn get_or_insert_with(&mut self, k: K, f: impl FnOnce() -> V) -> &mut V {
        let mut f = Some(f);
        self.at(k, &mut || (f.take().expect("one call"))())
    }

    /// The value of `k`, made by `make` when `k` is not a key; `make` runs at most once.
    fn at(&mut self, k: K, make: &mut dyn FnMut() -> V) -> &mut V {
        use std::collections::hash_map::Entry;
        let slot = match self.slots.entry(Self::slot(&k)) {
            Entry::Vacant(e) => {
                self.len += 1;
                return match e.insert(Slot::One(k, make())) {
                    Slot::One(_, v) => v,
                    Slot::Many(_) => unreachable!("a slot just made holds one key"),
                };
            }
            Entry::Occupied(e) => e.into_mut(),
        };
        if let Slot::One(key, _) = slot
            && *key != k
        {
            let Slot::One(key, v) = std::mem::replace(slot, Slot::Many(Default::default())) else {
                unreachable!("the slot held one key")
            };
            let Slot::Many(m) = slot else {
                unreachable!("the slot was just made a map")
            };
            m.insert(key, v);
        }
        match slot {
            Slot::One(_, v) => v,
            Slot::Many(m) => m.entry(k).or_insert_with(|| {
                self.len += 1;
                make()
            }),
        }
    }

    /// Takes `k` out, giving back its value.
    pub fn remove(&mut self, k: &K) -> Option<V> {
        self.remove_entry(k).map(|(_, v)| v)
    }

    /// Takes `k` out, giving back the key that was stored and its value.
    pub fn remove_entry(&mut self, k: &K) -> Option<(K, V)> {
        let h = Self::slot(k);
        let slot = self.slots.get_mut(&h)?;
        let kv = match slot {
            Slot::One(key, _) if &*key != k => return None,
            Slot::One(..) => match self.slots.remove(&h) {
                Some(Slot::One(key, v)) => (key, v),
                _ => unreachable!("the slot held one key"),
            },
            Slot::Many(m) => {
                let kv = m.remove_entry(k)?;
                if m.is_empty() {
                    self.slots.remove(&h);
                }
                kv
            }
        };
        self.len -= 1;
        Some(kv)
    }

    /// The keys and their values, in an order that changes from run to run with the seed of
    /// [`text_hash`]: a caller must reach no result through it.
    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.slots.values().flat_map(|slot| {
            let (one, many) = match slot {
                Slot::One(k, v) => (Some((k, v)), None),
                Slot::Many(m) => (None, Some(m.iter())),
            };
            one.into_iter().chain(many.into_iter().flatten())
        })
    }

    /// The values, in the order of [`TiedMap::iter`].
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.iter().map(|(_, v)| v)
    }
}

impl<K: Ord, V, H: KeyHash<K>> std::ops::Index<&K> for TiedMap<K, V, H> {
    type Output = V;
    fn index(&self, k: &K) -> &V {
        self.get(k).expect("a key of the map")
    }
}

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
///
/// A test fixes or varies the seed with the environment variable `ZED_TEXT_SEED`, a decimal
/// number below 2^64 ([`text_state`]). It holds foldhash's `SeedableRandomState`, which takes a
/// seed, where hashbrown's default (`foldhash::fast::RandomState`, which this replaced) takes
/// none; the cost is 8 more bytes per map (16 against 8) and no instruction per hash, since both
/// build `FoldHasher::with_seed` from a per-map seed and a reference to the shared seed.
#[derive(Clone, Debug)]
pub struct TextState(foldhash::fast::SeedableRandomState);

impl Default for TextState {
    /// A seed of its own: drawn at random, or, when `ZED_TEXT_SEED` is set, made from it and
    /// the number of states this thread made before ([`text_state`]).
    fn default() -> TextState {
        use foldhash::fast::SeedableRandomState;
        let Some((seed, shared)) = text_seed() else {
            return TextState(SeedableRandomState::random());
        };
        thread_local! {
            static MADE: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
        }
        let n = MADE.replace(MADE.get() + 1);
        TextState(SeedableRandomState::with_seed(step(seed, n), shared))
    }
}

impl std::hash::BuildHasher for TextState {
    type Hasher = foldhash::fast::FoldHasher<'static>;

    #[inline(always)]
    fn build_hasher(&self) -> Self::Hasher {
        self.0.build_hasher()
    }
}

/// `ZED_TEXT_SEED`, read once, with the shared seed foldhash makes from it; `None` when it is
/// unset. A value that is not a decimal number below 2^64 stops the run, so a test never runs
/// at random while it means to run at a seed.
fn text_seed() -> Option<(u64, &'static foldhash::SharedSeed)> {
    static SEED: std::sync::OnceLock<Option<(u64, foldhash::SharedSeed)>> =
        std::sync::OnceLock::new();
    let seed = SEED.get_or_init(|| {
        let s = std::env::var("ZED_TEXT_SEED").ok()?;
        let seed: u64 = (s.trim().parse())
            .unwrap_or_else(|_| panic!("ZED_TEXT_SEED is {s:?}, not a decimal number below 2^64"));
        Some((seed, foldhash::SharedSeed::from_u64(seed)))
    });
    seed.as_ref().map(|(n, shared)| (*n, shared))
}

impl TextState {
    /// The state of the process's one text hash (`TEXT`): at random, or, when `ZED_TEXT_SEED`
    /// is set, made from it alone, so that [`text_hash`] is one function of the seed whichever
    /// thread first hashes.
    fn of_process() -> TextState {
        use foldhash::fast::SeedableRandomState;
        match text_seed() {
            Some((seed, shared)) => TextState(SeedableRandomState::with_seed(seed, shared)),
            None => TextState(SeedableRandomState::random()),
        }
    }
}

/// A map keyed by a program's text, hashed by [`TextState`].
pub type TextMap<K, V> = HashMap<K, V, TextState>;

/// A set of keys made of a program's text, hashed by [`TextState`].
pub type TextSet<K> = HashSet<K, TextState>;

/// The one [`TextState`] of the process, seeded at random once: for a hash of text kept and
/// compared after the call that made it, such as a key made of the hash of a system of
/// constraints (`zedc_presburger`'s memos of repairs and its rows by terms), and for a
/// persistent map whose equal contents must hash and iterate alike in one run (`conjuncts`).
/// A [`TextMap`] that only looks keys up draws its own seed instead.
static TEXT: std::sync::LazyLock<TextState> = std::sync::LazyLock::new(TextState::of_process);

/// A copy of the process's one [`TextState`] (see `TEXT`).
///
/// The seed for tests (TEST-text-map-seed-determinism): when the environment variable
/// `ZED_TEXT_SEED` is set to a decimal number below 2^64, read once per process, every
/// [`TextState`] is made from it instead of at random. The process's one state, which this
/// copies and [`text_hash`] and [`text_hasher`] use, takes the seed itself; each other state,
/// a [`TextMap`]'s or [`TextSet`]'s own, takes [`step`] of the seed and the number of states its
/// thread made before, so that two maps still differ in order: with one hash function for every
/// table, one map's keys inserted into another in the first map's order fill the second's
/// slots in order, a quadratic case: rust-lang/rust issue 36481, 2016, "Exposure of HashMap
/// iteration order allows for O(n²) blowup" (read 2026-11-20 through the GitHub API, the issue
/// body): merging one map into another by `extend` took "0.4s" when the second map was
/// shuffled and "40.s" when it was not. The issue is still open, but the standard library's
/// `RandomState::new` (library/std/src/hash/random.rs at 4294891f4, read 2026-11-20) says "Later
/// in #36481 it was discovered that exposing a deterministic iteration order allows a form of
/// DOS attack. To counter that we increment one of the seeds on every RandomState creation";
/// the per-thread count of states mixed by [`step`] here is the same remedy. Unset, as in every run
/// that is not a test, each seed is drawn at random. A value that does not parse stops the run.
/// The tests `text_maps_reach_no_result_at_any_seed_*` (tests/steps/m0_12_refusal_census/
/// seeds.rs) check programs under several seeds and compare their output byte for byte.
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
/// The paper's "fast proposal is thus SipHash-2-4"; the standard library takes `c = 1, d = 3`:
/// library/std/src/hash/random.rs at 4294891f4 (read 2026-11-20) has `pub struct
/// DefaultHasher(SipHasher13)` and `DefaultHasher::new` is `SipHasher13::new_with_keys(0, 0)`,
/// though its documentation says "The internal algorithm is not specified, and so it and its
/// hashes should not be relied upon over releases"; here the key is `k0 = k1 = 0`, so the
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

    /// TEST-dry-shared-units: `step(0, x)` is SplitMix64's output for the state `x + γ` (Vigna's
    /// `splitmix64.c`: the state is advanced by γ = 0x9e3779b97f4a7c15, then mixed), so the step
    /// from 0 over 0, γ, 2γ gives the reference generator's first three outputs seeded with 0.
    /// The values were computed by a transcription of `splitmix64.c` apart from this crate
    /// (2026-11-20); they pin the constants `bdd::set::tests` relies on.
    #[test]
    fn the_step_from_zero_is_splitmix64() {
        const GAMMA: u64 = 0x9e37_79b9_7f4a_7c15;
        let outs: Vec<u64> = (0..3u64).map(|k| step(0, k.wrapping_mul(GAMMA))).collect();
        assert_eq!(
            outs,
            [
                0xe220_a839_7b1d_cdaf,
                0x6e78_9e6a_a1b9_65f4,
                0x06c4_5d18_8009_454f
            ]
        );
    }

    /// The step is a bijection in each argument (a rotation, an xor, an addition and the
    /// invertible finalizer), so no two of many words give one value from one `h`, and no two
    /// of many `h` from one word; and it depends on the order of the words. Negative control:
    /// a step that ignores `h` (only the finalizer of `x`) gives one value for every `h`, which
    /// the second check catches.
    #[test]
    fn the_step_is_one_to_one_in_each_argument_and_depends_on_order() {
        use std::collections::HashSet;
        let (mut rng, _) = crate::seed::Rng::fresh("the_step_is_one_to_one_in_each_argument");
        let words: Vec<u64> = (0..20_000)
            .map(|_| rng.next_u64())
            .chain([0, 1, u64::MAX])
            .collect();
        let h = rng.next_u64();
        let distinct = |f: &dyn Fn(u64) -> u64| words.iter().map(|&w| f(w)).collect::<HashSet<_>>();
        assert_eq!(distinct(&|x| step(h, x)).len(), words.len());
        assert_eq!(distinct(&|g| step(g, h)).len(), words.len());
        let ordered = |f: &dyn Fn(u64, u64) -> u64| {
            (words.windows(2))
                .filter(|w| w[0] != w[1])
                .all(|w| f(f(0, w[0]), w[1]) != f(f(0, w[1]), w[0]))
        };
        assert!(ordered(&step));
        let ignores_h = |_: u64, x: u64| step(0, x);
        assert_eq!(distinct(&|g| ignores_h(g, h)).len(), 1);
        assert!(
            !ordered(&|g, x| step(0, x) ^ g),
            "an xor of the words is caught as unordered"
        );
    }

    /// `ZED_TEXT_SEED` (TEST-kernel-num-rat-units), read once per process, so each case runs in
    /// a child process of this test binary that runs this test alone. In the child: the `n`-th
    /// [`TextState`] this thread makes is foldhash's state seeded with `step(seed, n)`, and the
    /// process's text hash ([`text_hash`], [`text_state`]) the one seeded with `seed` itself;
    /// with the variable unset, both are drawn at random. In the parent: a seed gives the same
    /// hashes in every run, two seeds differ, spaces around the number are trimmed, `2^64 - 1`
    /// is taken, `2^64` and a word stop the run naming the value, and two runs with no seed
    /// differ. Negative controls, each run once: `default` seeding the `n`-th state with
    /// `step(seed, n + 1)`, caught in the child; `text_seed` not trimming, caught in the parent.
    #[test]
    fn a_text_seed_fixes_every_text_hash_and_a_bad_one_stops_the_run() {
        use foldhash::fast::SeedableRandomState;
        const TEST: &str =
            "digest::tests::a_text_seed_fixes_every_text_hash_and_a_bad_one_stops_the_run";
        const CHILD: &str = "ZED_KERNEL_TEXT_SEED_CHILD";
        let words = ["", "x", "a name of more than sixteen bytes"];
        if std::env::var_os(CHILD).is_some() {
            let states = [TextState::default(), TextState::default()];
            let hashes = |s: &dyn Fn(&str) -> u64| words.map(s);
            let made = states.each_ref().map(|s| hashes(&|w| s.hash_one(w)));
            let process = hashes(&|w| text_hash(w));
            assert_eq!(process, hashes(&|w| text_state().hash_one(w)));
            if let Some((seed, shared)) = text_seed() {
                for (n, h) in made.iter().enumerate() {
                    let want = SeedableRandomState::with_seed(step(seed, n as u64), shared);
                    assert_eq!(*h, hashes(&|w| want.hash_one(w)), "state {n}");
                }
                let want = SeedableRandomState::with_seed(seed, shared);
                assert_eq!(process, hashes(&|w| want.hash_one(w)));
            }
            println!("hashes {made:?} {process:?}");
            return;
        }
        let run = |seed: Option<&str>| {
            let mut child = std::process::Command::new(std::env::current_exe().unwrap());
            child
                .args(["--exact", TEST, "--test-threads=1", "--nocapture"])
                .env(CHILD, "1")
                .env_remove("ZED_TEXT_SEED");
            if let Some(s) = seed {
                child.env("ZED_TEXT_SEED", s);
            }
            child.output().unwrap()
        };
        let hashes = |seed: Option<&str>| {
            let out = run(seed);
            let err = String::from_utf8_lossy(&out.stderr);
            assert!(out.status.success(), "ZED_TEXT_SEED={seed:?}: {err}");
            let text = String::from_utf8_lossy(&out.stdout);
            // The harness writes `test <name> ... ` before the line on the same line.
            let line = text.split_once("hashes [").map(|(_, h)| h.lines().next());
            line.flatten()
                .unwrap_or_else(|| panic!("no hashes: {text}"))
                .to_owned()
        };
        let at42 = hashes(Some("42"));
        assert_eq!(at42, hashes(Some("42")));
        assert_eq!(at42, hashes(Some(" 42\n")));
        assert_ne!(at42, hashes(Some("43")));
        assert_ne!(at42, hashes(Some(&u64::MAX.to_string())));
        assert_ne!(
            hashes(None),
            hashes(None),
            "unset, the seeds are drawn at random"
        );
        for bad in ["18446744073709551616", "x", ""] {
            let out = run(Some(bad));
            let err = String::from_utf8_lossy(&out.stderr);
            assert!(!out.status.success(), "{bad:?} was taken");
            let names = format!("ZED_TEXT_SEED is {bad:?}, not a decimal number below 2^64");
            assert!(err.contains(&names), "{bad:?}: {err}");
        }
    }
}
