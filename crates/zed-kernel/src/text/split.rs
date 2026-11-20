//! A piece of a text by code point ranks: [`Text::split_chars`] and [`Text::slice_chars`], the
//! kernel's half of DESIGN sec:optimizer "A piece of a string is a slice of its bytes"
//! (STUDY-string-slice-byte-offsets, the author's answer A107). `s.sliceCodePoints(a..<b)`,
//! defined as `Utf8String(s::codepoints.slice(a..<b))` (decode, take the ranks, encode), is the
//! bytes of `s` between the offsets of code points `a` and `b`; this module finds those offsets
//! by the code point counts the tree already keeps, and shares every block wholly inside the
//! piece, so nothing is decoded or encoded and only the two blocks the cuts fall in are read.
//!
//! Source. R. Hinze and R. Paterson, "Finger trees: a simple general-purpose data structure",
//! Journal of Functional Programming 16(2), 197-217, 2006, doi:10.1017/S0956796805005769
//! (the module comment of `text` gives what else is taken from it). Section 4.4, "Splitting",
//! is taken here: `splitTree` (`split_tree`), `splitDigit` (`split_digit`), and the smart
//! constructors `deepL` and `deepR` (`deep_l`, `deep_r`), which rebuild a deep tree whose
//! prefix or suffix the split left empty by taking the first or last node of the middle with
//! `viewL`/`viewR` (section 3.2, `view_l`, `view_r`). In the paper's words, "the cost of
//! splitTree is Θ(log(min{nl, nr})) ‘⊕’ operations", the measure here the monoid `Size` of
//! section 4.2, of which only `chars` is read. The predicate is "more than `i` code points so
//! far", which is monotone, as the paper requires, because every part holds at least one code
//! point (a block is not empty, and a non-empty `str` holds at least one character).
//! Checked 2026-11-20 against the text of section 4.4 (publisher's PDF, read whole).
//!
//! Departure: the paper's tree is lazy, and its `viewL` is `O(1)` amortized; here the tree is
//! strict (the module comment of `text`), so the `view_l` inside one `deep_l` may descend one
//! level per level of the middle when every prefix digit on the way holds one part. A split
//! descends at most `d` levels, `d ≤ log2(b/2 + 1)` for `b` blocks, and at each builds `O(1)`
//! nodes and calls one `deep_l` and one `deep_r` of at most `d` levels, so it builds `O(d²)` =
//! `O(log² b)` nodes in the worst case and `O(d)` when the digits it meets hold two or more
//! parts, as a chain of joins leaves them (section 3.2: only digits of one or four parts carry).
//! The bench `a_piece_of_a_text_of_n_blocks_costs_log_n` measures the case of a chain.
//!
//! The UTF-8 fact. RFC 3629 section 1, "Character boundaries are easily found from anywhere in
//! an octet stream": a code point's first byte is never of the form `10xxxxxx`, and every later
//! byte is. So the byte offset of code point `j` of a block is the offset of its `j`-th byte not
//! of that form ([`byte_of`]), one test of each byte read, with no decoding. (F. Yergeau, "UTF-8,
//! a transformation format of ISO 10646", RFC 3629, 2003, doi:10.17487/RFC3629; checked
//! 2026-11-20 against the RFC's text, section 1 and the table of section 3.)

use std::ops::Add;

use super::tree::{Digit, Size, Text, Tree};
use super::{block_of, count, deep, empty, push_back};

impl Text {
    /// The first `k` code points of the text and the rest, `k` clamped to
    /// [`Text::char_count`]: the two join to the text again. Every block wholly on one side is
    /// shared; the one block a cut falls inside is copied, as two blocks.
    // Complexity tradeoff: the naive piece writes the text out and takes `chars().take(k)`,
    // O(n) bytes read and decoded per piece, so a loop over the fields of a line costs
    // O(fields × n). Here the tree's kept code point counts lead to the block holding code
    // point `k` and the split of section 4.4 rebuilds the two sides from shared parts:
    // O(log² b) nodes built in the worst case of the strict tree, O(log b) on a chain of joins
    // (b the blocks), plus a scan of that one block, O(its bytes), to find the byte offset by
    // the RFC 3629 fact above. Given up: a block of a long literal (a 1 MiB literal is one
    // block) is scanned and its two pieces copied, O(the block); an index of code point offsets
    // per long block would make that O(log) and cost memory on every literal, which no measured
    // program needs. Proof of the result at `split_tree` and below. Tests
    // `text::split::tests`; bench `text::split::bench`.
    pub fn split_chars(&self, k: usize) -> (Text, Text) {
        if k == 0 {
            return (empty(), self.clone());
        }
        if k >= self.char_count() {
            return (self.clone(), empty());
        }
        // 0 < k < chars, so the code point ranked `k` exists, and `split_tree` gives the block
        // `x` holding it with `l` the blocks before: `l.chars ≤ k < l.chars + x.chars`.
        let (l, x, r) = split_tree(self, k);
        let Tree::Block { block, chars } = &*x.0 else {
            unreachable!("the parts of a text's own tree are blocks")
        };
        let j = k - l.char_count();
        let whole = |a: &Text, b: &Text| {
            Text::join(a, b).expect("a piece of a text is no longer than the text")
        };
        if j == 0 {
            // The cut is at the start of `x`: `l` | `x ++ r`, both of shared parts.
            return (l, whole(&x, &r));
        }
        // 0 < j < chars: both pieces of the block hold a code point, so neither is empty.
        let (p, q) = block.split_at(byte_of(block, j));
        (
            whole(&l, &block_of(p.into(), j)),
            whole(&block_of(q.into(), chars - j), &r),
        )
    }

    /// The code points ranked `a..<b` of the text, as a text keyed from 0: `a` and `b` clamped
    /// as DESIGN sec:optimizer clamps them, `a' = min(a, n)`, `b' = min(max(b, a'), n)` for
    /// `n` code points, so a range past the end or reversed gives the empty text. Two splits,
    /// so the cost of [`Text::split_chars`] twice.
    pub fn slice_chars(&self, a: usize, b: usize) -> Text {
        let n = self.char_count();
        let a = a.min(n);
        let b = b.clamp(a, n);
        self.split_chars(b).0.split_chars(a).1
    }
}

/// The byte offset of code point `j` of `s`, or `s.len()` when `s` has `j` code points: the
/// offset of the `j`-th byte that does not continue a code point (RFC 3629 section 1, the
/// module comment), `O(that offset)`.
fn byte_of(s: &str, j: usize) -> usize {
    s.bytes()
        .enumerate()
        .filter(|&(_, b)| b & 0xC0 != 0x80)
        .nth(j)
        .map_or(s.len(), |(i, _)| i)
}

/// The number of code points of the parts in `parts`.
fn chars_of(parts: &[Option<Text>]) -> usize {
    parts.iter().flatten().map(Text::char_count).sum()
}

/// The size of the parts in `parts`.
fn size_of(parts: &[Option<Text>]) -> Size {
    parts
        .iter()
        .flatten()
        .map(Text::size)
        .fold(Size::default(), Add::add)
}

/// The digit of `parts`, one to four `Some`s then `None`s.
fn digit_of(parts: &[Option<Text>]) -> Digit {
    debug_assert!((1..=4).contains(&count_of(parts)));
    std::array::from_fn(|i| parts.get(i).cloned().flatten())
}

/// The number of `Some`s of `parts`, which come before its `None`s.
fn count_of(parts: &[Option<Text>]) -> usize {
    parts.iter().take_while(|p| p.is_some()).count()
}

/// The tree of zero to four parts of one height, in order: `O(1)`.
fn tree_of(parts: &[Option<Text>]) -> Text {
    parts
        .iter()
        .flatten()
        .fold(empty(), |t, p| push_back(&t, p.clone()))
}

/// `t`, a tree of parts of one height, split at the part holding code point `i`, for
/// `i < t.char_count()`: the tree of the parts before it, that part, and the tree of the parts
/// after it, all three of `t`'s height of parts (the paper's `splitTree`).
///
/// Proof, by induction on the depth of `t`, of the two facts a caller relies on: (P1) the
/// parts of `l`, then `x`, then the parts of `r` are the parts of `t` in order, so their text
/// joined is `t`'s; (P2) `l.chars ≤ i < l.chars + x.chars`.
/// - `t` one part (a block or a node): `l` and `r` empty and `x = t`; (P1) at once, and (P2)
///   is `0 ≤ i < t.chars`, the precondition.
/// - `t` deep, `i` in the prefix (`i < vf`, `vf` the prefix's count): `split_digit` gives the
///   prefix's parts as `pl`, `x`, `pr` with `chars(pl) ≤ i < chars(pl) + x.chars` (its proof);
///   `l = tree_of(pl)` holds `pl`, and `deep_l(pr, m, sf)` holds `pr`, then `m`'s parts, then
///   `sf` (its proof), so (P1) and (P2) hold.
/// - `i` in the middle (`vf ≤ i < vf + m.chars`): by induction on `m`, one level higher,
///   `(ml, xs, mr)` with the parts of `m` in order and `ml.chars ≤ i − vf < ml.chars + xs.chars`;
///   `xs` is a node (the parts of a deep tree's middle are nodes), and `split_digit` of its two
///   or three parts at `i − vf − ml.chars` gives `nl`, `x`, `nr`; `deep_r(pr, ml, nl)` holds the
///   prefix, `ml`'s parts, `nl`, and `deep_l(nr, mr, sf)` holds `nr`, `mr`'s parts, the suffix,
///   so (P1) holds by the induction, and (P2) is `vf + ml.chars + chars(nl) ≤ i` and
///   `i < vf + ml.chars + chars(nl) + x.chars`, the two bounds added.
/// - `i` in the suffix: as the prefix, mirrored, with `vf + m.chars` subtracted.
///
/// The heights: `split_digit` returns parts of the digit's own height, `xs`'s parts are one
/// level below `m`'s parts, the height of `t`'s parts, so every tree built holds parts of one
/// height, the same as `t`'s; `deep`'s debug check of the sizes holds since each size is the
/// sum of the parts it is built from.
fn split_tree(t: &Text, i: usize) -> (Text, Text, Text) {
    match &*t.0 {
        Tree::Empty => unreachable!("a split of the empty tree, which holds no code point"),
        Tree::Block { .. } | Tree::Node { .. } => (empty(), t.clone(), empty()),
        Tree::Deep {
            front,
            middle,
            back,
            ..
        } => {
            let vf = chars_of(front);
            if i < vf {
                let (pl, x, pr) = split_digit(front, i);
                return (tree_of(pl), x, deep_l(pr, middle, back));
            }
            let vm = vf + middle.char_count();
            if i < vm {
                let (ml, xs, mr) = split_tree(middle, i - vf);
                let Tree::Node { parts, .. } = &*xs.0 else {
                    unreachable!("the parts of a deep tree's middle are nodes")
                };
                let (nl, x, nr) = split_digit(parts, i - vf - ml.char_count());
                return (deep_r(front, &ml, nl), x, deep_l(nr, &mr, back));
            }
            let (sl, x, sr) = split_digit(back, i - vm);
            (deep_r(front, middle, sl), x, tree_of(sr))
        }
    }
}

/// The parts of `parts` (`Some`s then `None`s) before the one holding code point `i`, that
/// part, and the parts after it, for `i` below their count. Proof: the scan stops at the first
/// part `x` whose count added to those before exceeds `i`, so `chars(before) ≤ i` (the scan did
/// not stop earlier) and `i < chars(before) + x.chars`; it stops, since the sum of all exceeds
/// `i`.
fn split_digit(parts: &[Option<Text>], mut i: usize) -> (&[Option<Text>], Text, &[Option<Text>]) {
    for (j, p) in parts.iter().enumerate() {
        let p = p.as_ref().expect("the code point lies within the parts");
        let c = p.char_count();
        if i < c {
            return (&parts[..j], p.clone(), &parts[j + 1..]);
        }
        i -= c;
    }
    unreachable!("the code point lies within the parts")
}

/// The deep tree of the prefix parts `pr`, the middle `m` and the suffix `sf`, when `pr` may
/// be empty (the paper's `deepL`): with `pr` empty, the first node of `m` becomes the prefix,
/// or, `m` empty too, the tree is the suffix's parts. Each way the parts are those of `pr`,
/// then `m`'s, then `sf`'s, in order: a node's parts are the parts it stands for.
fn deep_l(pr: &[Option<Text>], m: &Text, sf: &Digit) -> Text {
    if count_of(pr) > 0 {
        return deep(
            size_of(pr) + m.size() + size_of(sf),
            digit_of(pr),
            m.clone(),
            sf.clone(),
        );
    }
    match view_l(m) {
        None => tree_of(sf),
        Some((a, rest)) => {
            let Tree::Node { parts, .. } = &*a.0 else {
                unreachable!("the parts of a deep tree's middle are nodes")
            };
            deep(
                a.size() + rest.size() + size_of(sf),
                digit_of(parts),
                rest,
                sf.clone(),
            )
        }
    }
}

/// [`deep_l`] mirrored (the paper's `deepR`): the suffix `sf` may be empty.
fn deep_r(pr: &Digit, m: &Text, sf: &[Option<Text>]) -> Text {
    if count_of(sf) > 0 {
        return deep(
            size_of(pr) + m.size() + size_of(sf),
            pr.clone(),
            m.clone(),
            digit_of(sf),
        );
    }
    match view_r(m) {
        None => tree_of(pr),
        Some((rest, a)) => {
            let Tree::Node { parts, .. } = &*a.0 else {
                unreachable!("the parts of a deep tree's middle are nodes")
            };
            deep(
                size_of(pr) + rest.size() + a.size(),
                pr.clone(),
                rest,
                digit_of(parts),
            )
        }
    }
}

/// The first part of the tree `t` and the tree of the rest, or `None` for the empty tree (the
/// paper's `viewL`).
fn view_l(t: &Text) -> Option<(Text, Text)> {
    match &*t.0 {
        Tree::Empty => None,
        Tree::Block { .. } | Tree::Node { .. } => Some((t.clone(), empty())),
        Tree::Deep {
            front,
            middle,
            back,
            ..
        } => {
            let first = front[0].clone().expect("a digit holds a part");
            Some((first, deep_l(&front[1..], middle, back)))
        }
    }
}

/// The tree of all but the last part of `t`, and that part (the paper's `viewR`).
fn view_r(t: &Text) -> Option<(Text, Text)> {
    match &*t.0 {
        Tree::Empty => None,
        Tree::Block { .. } | Tree::Node { .. } => Some((empty(), t.clone())),
        Tree::Deep {
            front,
            middle,
            back,
            ..
        } => {
            let k = count(back);
            let last = back[k - 1].clone().expect("a digit holds a part");
            Some((deep_r(front, middle, &back[..k - 1]), last))
        }
    }
}

#[cfg(test)]
mod bench;

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::super::tests::{PIECE, assert_balanced, chain, join};
    use super::*;

    // Every expected piece is taken from a plain `String` by `chars`, never by the tree.

    /// The code points `a..<b` of `s`, clamped as `slice_chars` clamps them.
    fn want(s: &str, a: usize, b: usize) -> String {
        s.chars().skip(a).take(b.saturating_sub(a)).collect()
    }

    /// `t.slice_chars(a, b)` is well formed and reads as `want(s, a, b)`, and `split_chars`
    /// at `a` gives the two sides of `s` at that code point.
    fn agrees(t: &Text, s: &str, a: usize, b: usize) {
        let piece = t.slice_chars(a, b);
        assert_balanced(&piece);
        assert_eq!(piece.flat(), want(s, a, b), "the piece {a}..<{b}");
        let (l, r) = t.split_chars(a);
        assert_balanced(&l);
        assert_balanced(&r);
        let k = a.min(s.chars().count());
        let at = s.char_indices().nth(k).map_or(s.len(), |(i, _)| i);
        assert_eq!((&*l.flat(), &*r.flat()), s.split_at(at), "the split at {a}");
    }

    #[test]
    fn every_piece_of_a_chain_reads_as_the_str_piece() {
        // Chains of 1 to 13 blocks of 256 code points, each block of one width of one to four
        // bytes, joined from either end; every cut at a block's edge, one either side of it,
        // and past the end, against every other.
        for n in [1, 2, 3, 4, 5, 8, 13] {
            for left in [true, false] {
                let (t, s) = chain(n, left);
                let mut at: Vec<usize> = (0..=n)
                    .flat_map(|j| [j * PIECE, j * PIECE + 1, (j * PIECE).saturating_sub(1)])
                    .chain([n * PIECE + 7, usize::MAX])
                    .collect();
                at.sort_unstable();
                at.dedup();
                for &a in &at {
                    for &b in &at {
                        agrees(&t, &s, a, b);
                    }
                }
            }
        }
    }

    #[test]
    fn every_piece_of_texts_joined_in_any_order_reads_as_the_str_piece() {
        // Texts of 1 to 300 code points of mixed widths, joined in an order a random generator
        // picks, so that digits of one part, which send `deep_l` and `deep_r` into the middle,
        // occur; random pieces of each.
        let (mut rng, _) = crate::seed::Rng::fresh(
            "every_piece_of_texts_joined_in_any_order_reads_as_the_str_piece",
        );
        let mut pool: Vec<(Text, String)> = (1..=40)
            .map(|i| {
                let s = ["x", "ö", "日", "😀"][i % 4].repeat(1 + rng.below(300));
                (Text::from(s.as_str()), s)
            })
            .collect();
        for _ in 0..600 {
            let (i, j) = (rng.below(pool.len()), rng.below(pool.len()));
            if pool[i].1.len() + pool[j].1.len() > 1 << 16 {
                continue;
            }
            let t = join(&pool[i].0, &pool[j].0);
            let s = format!("{}{}", pool[i].1, pool[j].1);
            let n = s.chars().count();
            for _ in 0..8 {
                let (a, b) = (rng.below(n + 2), rng.below(n + 2));
                agrees(&t, &s, a, b);
            }
            pool.push((t, s));
        }
    }

    #[test]
    fn a_piece_shares_the_blocks_inside_it() {
        // A piece from the middle of a code point of block 1 to the middle of block 6 of a chain
        // of eight blocks holds blocks 2 to 5 themselves, not copies: their bytes are at the
        // addresses of the chain's.
        let (t, _) = chain(8, true);
        let held: HashSet<*const u8> = t.chunks().map(str::as_ptr).collect();
        let piece = t.slice_chars(PIECE + PIECE / 2, 6 * PIECE + PIECE / 2);
        let shared = piece
            .chunks()
            .filter(|c| held.contains(&c.as_ptr()))
            .count();
        assert_eq!(shared, 4, "the blocks of the piece wholly inside it");
        assert_eq!(piece.char_count(), 5 * PIECE);
    }

    #[test]
    fn pieces_at_the_ends_and_of_nothing() {
        let e = Text::from("");
        assert!(e.slice_chars(0, 5).is_empty());
        assert!(e.split_chars(3).0.is_empty() && e.split_chars(3).1.is_empty());
        let t = Text::from("a,b");
        assert_eq!(t.slice_chars(2, 3).flat(), "b");
        assert_eq!(t.slice_chars(2, 3), Text::from("b"));
        assert!(t.slice_chars(3, 2).is_empty(), "a reversed range is empty");
        assert_eq!(
            t.slice_chars(1, 99).flat(),
            ",b",
            "an end past the text is clamped"
        );
        let (l, r) = t.split_chars(0);
        assert!(l.is_empty() && r == t);
        let (l, r) = t.split_chars(3);
        assert!(l == t && r.is_empty());
    }

    #[test]
    fn the_byte_of_a_code_point_skips_continuation_bytes() {
        // One code point of each width, so each lead byte is followed by zero to three bytes of
        // the form 10xxxxxx (RFC 3629 section 3).
        let s = "aé日😀z";
        assert_eq!(
            (0..=5).map(|j| byte_of(s, j)).collect::<Vec<_>>(),
            [0, 1, 3, 6, 10, 11]
        );
        for j in 0..=5 {
            assert_eq!(
                byte_of(s, j),
                s.char_indices().nth(j).map_or(s.len(), |(i, _)| i)
            );
        }
    }
}
