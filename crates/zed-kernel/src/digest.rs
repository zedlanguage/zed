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
    /// Test hook: the bits of each slot's hash the map keys by. A unit test sets it to 0, so that
    /// every key shares one slot and the arms for a slot of two keys or more (`Slot::Many`) run
    /// in the normal build, where two keys of one hash are rare.
    #[cfg(test)]
    mask: u64,
}

/// A set of keys whose hashes a program can make tie: a [`TiedMap`] to `()`, with the methods
/// of a `HashSet`.
pub struct TiedSet<K, H = ByHash>(TiedMap<K, (), H>);

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
///
/// The ordered map is boxed so that a slot is no wider than its one key and value (plus the
/// tag): unboxed, a `BTreeMap` (3 words) set the width of every slot of a map of small keys,
/// and the table of slots holds one per key whether or not any key ties (test
/// `digest::tests::a_slot_is_as_wide_as_one_key_and_value`). Measured on the bench "checking a
/// body of unions" (l01_23 `deep_rec`), whose `Numbering::first` files every node:
/// PERF-row-hash-tied-digest (58e5bf7db) took its bytes from 1,964 M to 2,099 M at 8n
/// (PERF-check-body-of-unions-5.7pct-main). The box costs one allocation and one indirection
/// per tied hash, which only a tie pays.
enum Slot<K, V> {
    One(K, V),
    #[expect(
        clippy::box_collection,
        reason = "boxed so that a slot without a tie is as wide as its key and value"
    )]
    Many(Box<std::collections::BTreeMap<K, V>>),
}

impl<K, V, H> Default for TiedMap<K, V, H> {
    fn default() -> Self {
        TiedMap::new()
    }
}

impl<K, V, H> TiedMap<K, V, H> {
    /// An empty map; `const`, for a thread-local's initializer.
    pub const fn new() -> Self {
        TiedMap {
            slots: HashMap::with_hasher(BuildHasherDefault::new()),
            len: 0,
            hash: std::marker::PhantomData,
            #[cfg(test)]
            mask: !0,
        }
    }

    /// A map that keys by the bits `mask` of each slot's hash (test hook, see `mask`).
    #[cfg(test)]
    pub(crate) const fn with_mask(mask: u64) -> Self {
        let mut m = TiedMap::new();
        m.mask = mask;
        m
    }

    /// The number of slots whose keys tie (`Slot::Many`), for tests.
    #[cfg(test)]
    pub(crate) fn tied_slots(&self) -> usize {
        let many = |s: &&Slot<K, V>| matches!(s, Slot::Many(_));
        self.slots.values().filter(many).count()
    }

    /// The number of slots, for tests: none once the last key is out.
    #[cfg(test)]
    pub(crate) fn slot_count(&self) -> usize {
        self.slots.len()
    }

    /// Takes every key out.
    pub fn clear(&mut self) {
        self.slots.clear();
        self.len = 0;
    }
}

impl<K: Ord, V, H: KeyHash<K>> TiedMap<K, V, H> {
    /// Keeps the keys for which `keep` holds, given each key and its value.
    pub fn retain(&mut self, mut keep: impl FnMut(&K, &mut V) -> bool) {
        let mut len = 0;
        self.slots.retain(|_, slot| match slot {
            Slot::One(k, v) => {
                let kept = keep(k, v);
                len += usize::from(kept);
                kept
            }
            Slot::Many(m) => {
                m.retain(|k, v| keep(k, v));
                len += m.len();
                !m.is_empty()
            }
        });
        self.len = len;
    }
}

impl<K: Ord, V, H: KeyHash<K>> TiedMap<K, V, H> {
    /// The slot `k` is filed in: its hash by `H` hashed again by the process's seeded
    /// [`text_hash`]. A program can solve for keys whose hashes differ but fall in one probe
    /// sequence of an unseeded table (the flooding of [`DigestMap`]'s rule, KERNEL-bytype-
    /// flooding); with the seed, distinct hashes spread, and equal ones meet in one slot, where
    /// their order tells them apart.
    pub(crate) fn slot(&self, k: &K) -> u64 {
        let h = text_hash(&H::hash(k));
        #[cfg(test)]
        let h = h & self.mask;
        h
    }

    /// The place of `k`, filled or not, to fill with [`TiedEntry`]'s methods.
    pub fn entry(&mut self, k: K) -> TiedEntry<'_, K, V, H> {
        TiedEntry { map: self, key: k }
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
        match self.slots.get(&self.slot(k))? {
            Slot::One(key, v) => (key == k).then_some(v),
            Slot::Many(m) => m.get(k),
        }
    }

    /// The value of `k`, to change.
    pub fn get_mut(&mut self, k: &K) -> Option<&mut V> {
        let h = self.slot(k);
        match self.slots.get_mut(&h)? {
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
        let h = self.slot(&k);
        let slot = match self.slots.entry(h) {
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
        let h = self.slot(k);
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

impl<K: Ord, V, H: KeyHash<K>> Extend<(K, V)> for TiedMap<K, V, H> {
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, items: I) {
        for (k, v) in items {
            self.insert(k, v);
        }
    }
}

impl<K: Ord, V, H: KeyHash<K>> FromIterator<(K, V)> for TiedMap<K, V, H> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(items: I) -> Self {
        let mut m = TiedMap::new();
        m.extend(items);
        m
    }
}

impl<K, H> Default for TiedSet<K, H> {
    fn default() -> Self {
        TiedSet::new()
    }
}

impl<K, H> TiedSet<K, H> {
    /// An empty set; `const`, for a thread-local's initializer.
    pub const fn new() -> Self {
        TiedSet(TiedMap::new())
    }

    /// The number of keys.
    pub fn len(&self) -> usize {
        self.0.len
    }

    /// Whether the set holds no key.
    pub fn is_empty(&self) -> bool {
        self.0.len == 0
    }
}

/// Ids `0, 1, ...` for keys whose hashes a program can make tie, in the order the keys are first
/// met, so the ids are the same in every run though the [`TiedMap`] behind them is seeded. It is
/// `zed_collections::intern::Interner` with the keys of one hash kept in their order: a key tied
/// with `b` others costs `O(log b)` comparisons, not `O(b)` (PERF-typeset-tied-digest).
pub struct TiedInterner<K, H = ByHash> {
    ids: TiedMap<K, usize, H>,
    keys: Vec<K>,
}

impl<K, H> Default for TiedInterner<K, H> {
    fn default() -> Self {
        TiedInterner {
            ids: TiedMap::new(),
            keys: Vec::new(),
        }
    }
}

impl<K: Ord + Clone, H: KeyHash<K>> TiedInterner<K, H> {
    /// The id of `k`, the next unused one when `k` is met for the first time.
    pub fn intern(&mut self, k: K) -> usize {
        // Two searches for a key met the first time, one for every later meeting: one search
        // through `get_or_insert_with` would need a clone of `k` for `keys` before it knows
        // whether `k` is new, and a clone of a big integer or a type allocates on every hit.
        if let Some(&i) = self.ids.get(&k) {
            return i;
        }
        let i = self.keys.len();
        self.keys.push(k.clone());
        self.ids.insert(k, i);
        i
    }

    /// The id of `k`, if it has one.
    pub fn id(&self, k: &K) -> Option<usize> {
        self.ids.get(k).copied()
    }
}

impl<K, H> TiedInterner<K, H> {
    /// The number of ids given.
    pub fn len(&self) -> usize {
        self.keys.len()
    }

    /// Whether no id was given.
    pub fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }

    /// The keys, by id.
    pub fn values(&self) -> &[K] {
        &self.keys
    }

    /// The keys, by id, taken out.
    pub fn into_values(self) -> Vec<K> {
        self.keys
    }
}

/// The keys and values, taken out, in the order of [`TiedMap::iter`].
impl<K, V, H> IntoIterator for TiedMap<K, V, H> {
    type Item = (K, V);
    type IntoIter = TiedIntoIter<K, V>;
    fn into_iter(self) -> TiedIntoIter<K, V> {
        TiedIntoIter {
            slots: self.slots.into_values(),
            tied: None,
        }
    }
}

/// The keys and values of a [`TiedMap`], taken out.
pub struct TiedIntoIter<K, V> {
    slots: std::collections::hash_map::IntoValues<u64, Slot<K, V>>,
    /// The rest of the slot of tied keys being taken out.
    tied: Option<std::collections::btree_map::IntoIter<K, V>>,
}

impl<K, V> Iterator for TiedIntoIter<K, V> {
    type Item = (K, V);
    fn next(&mut self) -> Option<(K, V)> {
        loop {
            if let Some(kv) = self.tied.as_mut().and_then(Iterator::next) {
                return Some(kv);
            }
            match self.slots.next()? {
                Slot::One(k, v) => return Some((k, v)),
                Slot::Many(m) => self.tied = Some(m.into_iter()),
            }
        }
    }
}

impl<K: Ord, H: KeyHash<K>> TiedSet<K, H> {
    /// Puts `k` in, giving whether it was not there.
    pub fn insert(&mut self, k: K) -> bool {
        self.0.insert(k, ()).is_none()
    }

    /// Whether `k` is in the set.
    pub fn contains(&self, k: &K) -> bool {
        self.0.contains_key(k)
    }

    /// Takes `k` out, giving whether it was there.
    pub fn remove(&mut self, k: &K) -> bool {
        self.0.remove(k).is_some()
    }

    /// The keys, in an order that changes from run to run ([`TiedMap::iter`]).
    pub fn iter(&self) -> impl Iterator<Item = &K> {
        self.0.iter().map(|(k, _)| k)
    }
}

impl<K: Ord, H: KeyHash<K>> Extend<K> for TiedSet<K, H> {
    fn extend<I: IntoIterator<Item = K>>(&mut self, items: I) {
        self.0.extend(items.into_iter().map(|k| (k, ())));
    }
}

impl<K: Ord, H: KeyHash<K>> FromIterator<K> for TiedSet<K, H> {
    fn from_iter<I: IntoIterator<Item = K>>(items: I) -> Self {
        let mut s = TiedSet::new();
        s.extend(items);
        s
    }
}

/// The place of a key in a [`TiedMap`], filled or not.
pub struct TiedEntry<'a, K, V, H> {
    map: &'a mut TiedMap<K, V, H>,
    key: K,
}

impl<'a, K: Ord, V, H: KeyHash<K>> TiedEntry<'a, K, V, H> {
    /// The key's value, put there by `f` when the key is not in the map.
    pub fn or_insert_with(self, f: impl FnOnce() -> V) -> &'a mut V {
        self.map.get_or_insert_with(self.key, f)
    }

    /// The key's value, `v` when the key is not in the map.
    pub fn or_insert(self, v: V) -> &'a mut V {
        self.or_insert_with(|| v)
    }

    /// The key's value, the default when the key is not in the map.
    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        self.or_insert_with(V::default)
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

/// The digest `h` with the word `x` added, the step of [`Digest`]: zed-hash's splitmix64 step,
/// where its constants, citations, proof and tests are (DRY-hash-crate-2026-11-26).
pub use zed_hash::step;

#[cfg(test)]
mod tests {
    use super::*;
    use std::hash::{BuildHasher, BuildHasherDefault};

    fn of(f: impl FnOnce(&mut Digest)) -> u64 {
        let mut d = Digest::default();
        f(&mut d);
        d.finish()
    }

    /// A [`TiedMap`] slot is at most one word wider than its key and value, for the keys of
    /// `Numbering::first` (a handle and a class number) and of the maps of types (one handle):
    /// the ordered map of a tie is boxed (PERF-check-body-of-unions-5.7pct-main). Unboxed, the
    /// map's three words made the first slot 32 bytes against a pair of 16, and this fails.
    #[test]
    fn a_slot_is_as_wide_as_one_key_and_value() {
        use std::mem::size_of;
        use std::sync::Arc;
        let word = size_of::<usize>();
        assert!(size_of::<Slot<Arc<u8>, u32>>() <= size_of::<(Arc<u8>, u32)>() + word);
        assert!(size_of::<Slot<Arc<u8>, usize>>() <= size_of::<(Arc<u8>, usize)>() + word);
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
