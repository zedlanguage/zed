//! The spelling index of step L1.29e (DESIGN.md sec:diagnostics, "Nearest in spelling"): for
//! all the written names of a unit together, the name visible at each one's site that is near
//! it in spelling, the first in name order, or none.
//!
//! A name is near in spelling to a written name when the two differ by one slip (one character
//! inserted, deleted or replaced, or two adjacent characters swapped), or are equal once ASCII
//! letters are lowercased and underscores dropped (`myVar` and `my_var`); equal names are not
//! near. Name order is the order of the spellings as strings (`str`'s `Ord`, the order of
//! their bytes), the order the resolver's `BTreeSet`s of names keep.
//!
//! Method. Every visible name is filed under keys, and every written name looks up keys, so
//! that each name near a written one shares a key with it (proof at [`nearest`]):
//! - a name `c` is filed under its own hash, its length kept with it (`Own`); under the hash of
//!   each string it gives with one character deleted, once without the position (`Del`) and
//!   once with it (`DelAt`); and under the hash of its folded spelling (`Fold`);
//! - a written name `w` looks up `Del` with its own hash (a name that is `w` with a character
//!   inserted), `Own` with each of its deletions (a name that is `w` with one deleted), `DelAt`
//!   with each of its deletions at the same position (one replaced), `Own` with each of its
//!   adjacent swaps (two swapped), and `Fold` with its folded hash.
//!
//! This is the deletion method of M. Mor and A. S. Fraenkel, "A hash code method for detecting
//! and correcting spelling errors", Communications of the ACM 25(12):935-938, 1982
//! (doi:10.1145/358728.358752), with the positions of DESIGN.md's index added: the full comment
//! with how it was checked is at zedc-resolve `SpellingIndex`, which uses it for one name at a
//! time. The hashes are the polynomial hashes of R. M. Karp and M. O. Rabin, "Efficient
//! randomized pattern-matching algorithms", IBM Journal of Research and Development 31(2):249-
//! 260, 1987 (doi:10.1147/rd.312.0249; the full comment is at zed-kernel `Text::poly_hash`),
//! modulo the Mersenne prime `2^61 - 1` of zed-numtheory `m61`: with prefix hashes
//! `H[k] = Σ_(j<k) (c_j + 1) B^(k-1-j)`, the hash of a string with the character at `i` deleted
//! and the hash with `i` and `i + 1` swapped are each O(1) from `H` and the powers of `B`
//! (`Hashes::deleted`, `Hashes::swapped`), so no key string is ever built.
//!
//! A name is visible from its declaration to the end of its scope, given here as a half-open
//! range of places `from..to`, the places of the written names in the same numbering. The
//! lookups of a unit are answered together, in one sweep of the places in order: at each place
//! the names whose range ends there leave their keys, the names whose range starts there join
//! them, and the written names there are answered. Each key keeps its visible names by rank in
//! name order with a count of the declarations that give each (a `BTreeMap`), so its first is a
//! map lookup. A written name takes the least first rank over its keys, and the spellings of
//! the two are compared before the name is offered (`near_in_spelling`): a name whose hash
//! matches but whose spelling does not is skipped, and its key gives its next name.
//
// Complexity tradeoff (DESIGN.md sec:diagnostics, "Nearest in spelling"): the least edit
// distance is not the measure, because no search for it runs in O(n log n): edit distance
// cannot be computed in time O(n^(2-δ)) for any δ > 0 unless the Strong Exponential Time
// Hypothesis is false (A. Backurs and P. Indyk, "Edit distance cannot be computed in strongly
// subquadratic time (unless SETH is false)", STOC 2015, doi:10.1145/2746539.2746612,
// arXiv:1412.0348; cited from DESIGN.md's [BackursIndyk] and from memory of the title and main
// theorem, not reread 2026-11-24). The naive search computes the edit distance from each of q
// written names to each of m visible names of length up to l, O(q·m·l²). Here, for n the total
// length of all names and written names: the hashes cost O(n); a name of length l is filed
// under 2l + 2 keys and a written name of length l looks up at most 3l + 1, so the sweep makes
// O(n) map updates and lookups of O(log n) each; the ranks come from one sort of the distinct
// spellings, O(n log n) character comparisons, since each comparison costs at most the
// shorter string's length plus one and each string takes part in O(log n) of them in a merge
// sort. So O(n log n) in all, plus one O(l + |c|) spelling comparison for each name `c` whose
// hash matches a key of a written name of length l without being near it: such a match is a
// hash collision (two different strings of length at most max(l, |c|) colliding modulo
// `2^61 - 1`, probability at most max(l, |c|) / 2^61 for a random base, Karp and Rabin's
// bound) or the written name's own spelling, which is skipped by rank before any comparison.
// The base below is fixed, so the bound holds for inputs not built against this base; a
// crafted input can force collisions, and then only the cost grows, never the answer, since
// every name offered is compared in full first. The tradeoff is that a name two slips away
// is not offered. Tests: the cases of step L1.29e's test in
// tests/steps/l01_29_diagnostics/spelling_index.rs; the random battery
// `tests::the_index_agrees_with_a_check_of_each_pair`; the scaling bench
// `bench::the_spelling_index_takes_n_log_n`.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BinaryHeap, HashMap};
use std::ops::Range;

use zed_numtheory::m61::{P, Prefix, add, mul, powers, sub};

use crate::intern::Interner;

/// `s` with ASCII letters lowercased and underscores dropped.
pub fn fold(s: &str) -> String {
    (s.chars())
        .filter(|&c| c != '_')
        .map(|c| c.to_ascii_lowercase())
        .collect()
}

/// Whether `written` and `name` are near in spelling (DESIGN.md sec:diagnostics, "Nearest in
/// spelling"): they differ by one slip, one character inserted, deleted or replaced or two
/// adjacent characters swapped, or they are equal once ASCII letters are lowercased and
/// underscores dropped. Equal names are not near. O(|written| + |name|) time.
pub fn near_in_spelling(written: &str, name: &str) -> bool {
    let a: Vec<char> = written.chars().collect();
    let b: Vec<char> = name.chars().collect();
    if a == b {
        return false;
    }
    if fold(written) == fold(name) {
        return true;
    }
    // The first and the last place where the two differ, from each end.
    let head = a.iter().zip(&b).take_while(|(x, y)| x == y).count();
    let tail = (a.iter().rev().zip(b.iter().rev()))
        .take_while(|(x, y)| x == y)
        .count();
    let (short, long) = if a.len() <= b.len() {
        (&a, &b)
    } else {
        (&b, &a)
    };
    match long.len() - short.len() {
        // One character inserted or deleted: the shorter is the longer with one dropped.
        1 => head + tail >= short.len(),
        // One replaced, or two adjacent swapped.
        0 => {
            let n = a.len();
            head + tail + 1 == n
                || (head + tail + 2 == n && a[head] == b[head + 1] && a[head + 1] == b[head])
        }
        _ => false,
    }
}

/// The base of the hashes, below `P`: an odd number with bits spread over the word, fixed so
/// that each run files the same keys (see the complexity comment at the head of this file).
const BASE: u64 = 0x0f3d_5b79_a2c4_e681 % P;

/// A key a name is filed under: a kind, the length of the string hashed, the position of the
/// deleted character for `DelAt` (else `u32::MAX`), and the hash.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Key(Kind, u32, u32, u64);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Kind {
    Own,
    Del,
    DelAt,
    Fold,
}

/// The prefix hashes of one string ([`Prefix`]) and its characters.
struct Hashes {
    /// `pre.get(k)`, the hash of the first `k` characters.
    pre: Prefix,
    /// The characters, each as `c + 1`, below `P`.
    chars: Vec<u64>,
}

impl Hashes {
    fn new(s: &str) -> Self {
        let chars: Vec<u64> = s.chars().map(|c| u64::from(c) + 1).collect();
        let pre = Prefix::new(BASE, chars.iter().copied());
        Hashes { pre, chars }
    }

    fn len(&self) -> usize {
        self.chars.len()
    }

    /// The hash of the whole string.
    fn whole(&self) -> u64 {
        self.pre.whole()
    }

    /// The hash of the string with the character at `i` deleted:
    /// `H[i] B^(n-1-i) + (H[n] - H[i+1] B^(n-1-i))`, the prefix before `i` shifted past the
    /// suffix after it, plus that suffix (Horner's rule split at `i`).
    fn deleted(&self, i: usize, pow: &[u64]) -> u64 {
        let n = self.len();
        let suffix = self.pre.span(i + 1, n, pow);
        add(mul(self.pre.get(i), pow[n - 1 - i]), suffix)
    }

    /// The hash of the string with the characters at `i` and `i + 1` swapped: the character at
    /// `i` carries the weight `B^(n-1-i)` and the one at `i + 1` the weight `B^(n-2-i)`, so the
    /// swap adds `(c_(i+1) - c_i)(B^(n-1-i) - B^(n-2-i))`.
    fn swapped(&self, i: usize, pow: &[u64]) -> u64 {
        let n = self.len();
        let (a, b) = (self.chars[i], self.chars[i + 1]);
        let diff = sub(pow[n - 1 - i], pow[n - 2 - i]);
        add(self.whole(), mul(sub(b, a), diff))
    }
}

/// The hash of `fold(s)`.
fn folded_hash(s: &str) -> u64 {
    Hashes::new(&fold(s)).whole()
}

/// A length or position as a key's `u32`; names longer than `u32::MAX` characters cannot be
/// written in a source the loader reads (its size is held in a `u32` span).
fn key_len(n: usize) -> u32 {
    u32::try_from(n).expect("a name's length fits in u32")
}

/// For each written name `(w, at)`, the name of `names` near `w` in spelling and visible at
/// `at` (`from <= at < to` for some `(name, from..to)` of `names`), the first in name order;
/// `None` when no visible name is near. A name declared twice is visible where either range
/// holds it.
///
/// Every near name is found (proof). Let `c` be visible at `at` and near `w`. If `fold(c) =
/// fold(w)`, `c` is filed under `Fold` with the hash `w` looks up. Otherwise they differ by one
/// slip: (1) `c` is `w` with a character inserted at `i`: `c` with `i` deleted is `w`, so `c`'s
/// `Del` key of length `|w|` has `w`'s hash; (2) `c` is `w` with the character at `i` deleted:
/// `c`'s `Own` key is `w`'s deletion at `i`; (3) the character at `i` replaced: `c` and `w`
/// with `i` deleted are equal and of the same position, `DelAt`; (4) the characters at `i` and
/// `i + 1` swapped, which differ since `c != w`: `c`'s `Own` key is `w`'s swap at `i`. Equal
/// strings have equal hashes, so in each case `c` is in a key `w` looks up, visible there at
/// the sweep's step for `at`. The written name takes the least rank over its keys' first
/// names, so the least rank of all near names is reached before any larger one; and every name
/// offered passed `near_in_spelling`, so it is near. A name that fails is a hash collision
/// or `w` itself: it is passed over in its key only, and the key's next name is taken, so a
/// near name in the same key is still reached.
pub fn nearest<'a>(
    names: &[(&'a str, Range<usize>)],
    written: &[(&str, usize)],
) -> Vec<Option<&'a str>> {
    // The distinct spellings in name order, and each one's rank.
    let mut spellings: Vec<&'a str> = names.iter().map(|(n, _)| *n).collect();
    crate::sorted::sort_dedup(&mut spellings);
    let rank: HashMap<&str, u32> = (spellings.iter().enumerate())
        .map(|(r, s)| (*s, key_len(r)))
        .collect();
    let longest = (names.iter().map(|(n, _)| n.chars().count()))
        .chain(written.iter().map(|(w, _)| w.chars().count()))
        .max()
        .unwrap_or(0);
    let pow = powers(BASE, longest);

    // The keys each spelling is filed under, by id.
    let mut keys: Interner<Key> = Interner::default();
    let filed: Vec<Vec<usize>> = (spellings.iter())
        .map(|s| {
            let h = Hashes::new(s);
            let n = key_len(h.len());
            let mut ks = vec![
                keys.intern(Key(Kind::Own, n, u32::MAX, h.whole())),
                keys.intern(Key(Kind::Fold, 0, u32::MAX, folded_hash(s))),
            ];
            for i in 0..h.len() {
                let d = h.deleted(i, &pow);
                ks.push(keys.intern(Key(Kind::Del, n - 1, u32::MAX, d)));
                ks.push(keys.intern(Key(Kind::DelAt, n - 1, key_len(i), d)));
            }
            ks
        })
        .collect();

    // The sweep: at each place, the ranges ending there leave, those starting there join,
    // then the written names there are answered.
    #[derive(PartialEq, Eq, PartialOrd, Ord)]
    enum Step {
        Leave(u32),
        Join(u32),
        Ask(usize),
    }
    let mut steps: Vec<(usize, Step)> = Vec::with_capacity(2 * names.len() + written.len());
    for (n, r) in names.iter().filter(|(_, r)| r.start < r.end) {
        steps.push((r.start, Step::Join(rank[n])));
        steps.push((r.end, Step::Leave(rank[n])));
    }
    steps.extend(
        written
            .iter()
            .enumerate()
            .map(|(i, (_, at))| (*at, Step::Ask(i))),
    );
    steps.sort_unstable();

    let mut visible: Vec<BTreeMap<u32, u32>> = vec![BTreeMap::new(); keys.len()];
    let mut out = vec![None; written.len()];
    for (_, step) in steps {
        match step {
            Step::Join(r) => {
                for &k in &filed[r as usize] {
                    *visible[k].entry(r).or_default() += 1;
                }
            }
            Step::Leave(r) => {
                for &k in &filed[r as usize] {
                    let count = visible[k]
                        .get_mut(&r)
                        .expect("a name leaves a key it joined");
                    *count -= 1;
                    if *count == 0 {
                        visible[k].remove(&r);
                    }
                }
            }
            Step::Ask(i) => {
                let w = written[i].0;
                let looked = lookups(w, &pow).filter_map(|k| keys.id(&k));
                out[i] = first_near(w, rank.get(w).copied(), looked, &visible, &spellings);
            }
        }
    }
    out
}

/// The keys `w` looks up (see the head of this file): `Del` with its own hash, `Own` and
/// `DelAt` with each deletion, `Own` with each adjacent swap of two different characters, and
/// `Fold` with its folded hash.
fn lookups<'p>(w: &str, pow: &'p [u64]) -> impl Iterator<Item = Key> + 'p {
    let h = Hashes::new(w);
    let n = key_len(h.len());
    let fixed = [
        Key(Kind::Del, n, u32::MAX, h.whole()),
        Key(Kind::Fold, 0, u32::MAX, folded_hash(w)),
    ];
    let len = h.len();
    let dels: Vec<Key> = (0..len)
        .flat_map(|i| {
            let d = h.deleted(i, pow);
            [
                Key(Kind::Own, n - 1, u32::MAX, d),
                Key(Kind::DelAt, n - 1, key_len(i), d),
            ]
        })
        .collect();
    let swaps: Vec<Key> = (0..len.saturating_sub(1))
        .filter(|&i| h.chars[i] != h.chars[i + 1])
        .map(|i| Key(Kind::Own, n, u32::MAX, h.swapped(i, pow)))
        .collect();
    fixed.into_iter().chain(dels).chain(swaps)
}

/// The first name in name order among the keys `looked`, other than `w`'s own spelling (rank
/// `own`), that is near `w`: a heap holds each key's least rank not yet passed over, and the
/// least of all is compared with `w` in full; one that is not near is passed over in its key.
fn first_near<'a>(
    w: &str,
    own: Option<u32>,
    looked: impl Iterator<Item = usize>,
    visible: &[BTreeMap<u32, u32>],
    spellings: &[&'a str],
) -> Option<&'a str> {
    let next = |k: usize, after: Option<u32>| {
        let from = after.map_or(0, |r| r + 1);
        (visible[k].range(from..).map(|(&r, _)| r)).find(|&r| Some(r) != own)
    };
    let mut heap: BinaryHeap<Reverse<(u32, usize)>> = looked
        .filter_map(|k| next(k, None).map(|r| Reverse((r, k))))
        .collect();
    while let Some(Reverse((r, k))) = heap.pop() {
        let c = spellings[r as usize];
        if near_in_spelling(w, c) {
            return Some(c);
        }
        if let Some(r2) = next(k, Some(r)) {
            heap.push(Reverse((r2, k)));
        }
    }
    None
}

#[cfg(test)]
mod tests;
