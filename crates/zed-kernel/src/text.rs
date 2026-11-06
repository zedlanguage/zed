//! The text of a string value, for the kernel and the native runtime alike. A string joined by
//! `++` is kept as a tree whose leaves are blocks of text, and a string is still compared,
//! ordered and printed by its text alone (DESIGN.md: "ropes are a representation and never
//! enter identity").
//!
//! The tree is an AVL tree: the heights of a node's two parts differ by at most 1, so its
//! height is at most `1.44 log2` of its number of leaves (at most 92 for a string of
//! `usize::MAX` bytes), and every walk over it, reading or dropping, is that deep. A join builds
//! `O(log n)` new nodes and shares the rest of both parts, so holding every prefix of a chain of
//! `n` joins keeps `O(n log n)` memory, and joining `n` pieces one at a time, as a `foldl` of
//! `++` does, costs `O(n log n)` (COMPLEXITY.md C29).
//!
//! Nothing is written out and kept: readers walk the leaves in order ([`Text::chunks`]), so a
//! comparison stops at the first byte that differs, in `O(log n)` plus the bytes it reads;
//! hashing and printing cost the text's length. A reader that needs the text as one `&str`
//! gets it from [`Text::flat`], which borrows a single block and writes a join into a new
//! `String` at each call.
//!
//! Each node keeps its length in bytes and in characters, added when two are joined, so `len`
//! is `O(1)` and reads no text (COMPLEXITY.md R4, R5).

use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use num_bigint::BigUint;

use crate::KernelError;
use crate::num::TooLarge;

/// A string's text, shared.
#[derive(Clone)]
pub struct Text(Arc<Node>);

struct Node {
    /// The length of the text in bytes.
    len: usize,
    /// The length of the text in characters (Unicode scalar values), what `len` gives.
    chars: usize,
    /// The number of joins on the longest path to a leaf: 0 for a leaf.
    height: u8,
    body: Body,
}

enum Body {
    /// A block of text; empty only in a text that is empty.
    Leaf(Arc<str>),
    /// A join of two texts, neither empty, whose heights differ by at most 1.
    Join(Text, Text),
}

// Complexity tradeoff: a join of two texts whose bytes fit in `LEAF` together, or of a short
// text to the end block of a longer one, copies them into one block of at most `LEAF` bytes,
// `O(LEAF)` work and memory per join. Cost: a join that would otherwise only share its parts
// copies up to `LEAF` bytes, so `n` prefixes held keep up to `LEAF` bytes each besides their
// `O(log n)` nodes. Given up: nothing in order; the result and every reader are the same. Why:
// a string built a character at a time would otherwise hold a node of about 56 bytes and a
// block of 16 bytes of counts for each character, and every read would walk that many leaves.
// Measured (WRITE-prefix-scale merge, release, load 62 to 69, a `foldl` of 200,000 joins of
// one piece, merging on against off): 1-byte pieces, 1,563 leaves of height 11 against
// 200,000 of height 18, `==` of two such texts 0.2 ms against 34 to 40 ms, a hash 0.3 to 3.6
// ms against 22 to 24 ms, printing 0.3 to 1.3 ms against 18 to 23 ms; 8-byte pieces, `==` 2 to
// 5 ms against 11 to 39 ms; 128-byte pieces, which never merge, the same. One more effect: a
// join of at most `LEAF` bytes is one block ([`Text::is_flat`]), so staging keys a call at it
// by its answers (`zedc::stage::compared`) and a call at a longer join by the function's term;
// the value is the same either way. Trigger: a join whose parts' adjacent blocks are short.
// Test: `text::tests::a_string_built_a_character_at_a_time_is_held_in_blocks`; COMPLEXITY.md
// C29. A solution with no constant would need leaves whose size follows the text's own pieces
// with no per-piece node, which no structure here has; the amortized O(1) append of plan row
// TEXT-append-O1 still needs a leaf size.
const LEAF: usize = 128;

impl Text {
    /// The text `a` then `b`. A join shares both parts and builds `O(log n)` new nodes for a
    /// text of `n` leaves; it copies no more than `LEAF` bytes. A join shares its parts, so a
    /// string doubled 64 times is a few dozen nodes and `2^64` times as long as the first:
    /// when the two lengths in bytes add up past `usize::MAX` the join's length is not
    /// representable, and it is refused with [`KernelError::StringTooLong`].
    pub fn join(a: &Text, b: &Text) -> Result<Text, KernelError> {
        if a.0.len == 0 {
            return Ok(b.clone());
        }
        if b.0.len == 0 {
            return Ok(a.clone());
        }
        if a.0.len.checked_add(b.0.len).is_none() {
            return Err(KernelError::StringTooLong {
                left: a.0.len,
                right: b.0.len,
            });
        }
        if let Body::Leaf(s) = &b.0.body
            && let Some(t) = a.with_last(s, b.0.chars)
        {
            return Ok(t);
        }
        if let Body::Leaf(s) = &a.0.body
            && let Some(t) = b.with_first(s, a.0.chars)
        {
            return Ok(t);
        }
        Ok(concat(a, b))
    }

    /// The length in bytes, without reading the text.
    pub fn len(&self) -> usize {
        self.0.len
    }

    /// Whether the text is empty.
    pub fn is_empty(&self) -> bool {
        self.0.len == 0
    }

    /// The number of characters, Unicode scalar values, without reading the text.
    pub fn char_count(&self) -> usize {
        self.0.chars
    }

    /// Whether the text is held as one block, so [`Text::flat`] copies nothing and a reader
    /// walks no tree: a join, of any length, is held in parts and never written out.
    pub fn is_flat(&self) -> bool {
        matches!(self.0.body, Body::Leaf(_))
    }

    /// The blocks of the text from left to right, none empty. The walk keeps its own stack,
    /// as deep as the tree: `O(log n)` for the first block, and every block in `O(len)`.
    pub fn chunks(&self) -> Chunks<'_> {
        let mut todo = Vec::with_capacity(usize::from(self.0.height) + 1);
        todo.push(self);
        Chunks { todo }
    }

    /// The text as one `&str`: a text held as one block is borrowed; a join is written into a
    /// new `String` at each call, `O(len)`, and not kept, so holding a text never holds a
    /// second copy of it. For readers that need one `&str`, as `lower` and a cast do.
    pub fn flat(&self) -> Cow<'_, str> {
        match &self.0.body {
            Body::Leaf(s) => Cow::Borrowed(s),
            Body::Join(..) => {
                let mut out = String::with_capacity(self.0.len);
                self.chunks().for_each(|c| out.push_str(c));
                Cow::Owned(out)
            }
        }
    }

    /// The text as one `&str`, as [`Text::flat`] gives it, with a join written into memory the
    /// system gives first for all of it; [`TooLarge`] when it refuses, naming that memory, so
    /// a reader of a text too long to copy, as a cast is, reports it and does not abort.
    pub fn try_flat(&self) -> Result<Cow<'_, str>, TooLarge> {
        match &self.0.body {
            Body::Leaf(s) => Ok(Cow::Borrowed(s)),
            Body::Join(..) => {
                let mut out = String::new();
                out.try_reserve_exact(self.0.len).map_err(|_| TooLarge {
                    bits: BigUint::from(self.0.len) << 3u32,
                })?;
                self.chunks().for_each(|c| out.push_str(c));
                Ok(Cow::Owned(out))
            }
        }
    }

    /// `self` with `s`, of `chars` characters, added to its last block, when the two fit in
    /// one leaf; each node on the way is rebuilt with its height unchanged.
    fn with_last(&self, s: &str, chars: usize) -> Option<Text> {
        match &self.0.body {
            Body::Leaf(last) => (last.len() + s.len() <= LEAF)
                .then(|| leaf([&**last, s].concat().into(), self.0.chars + chars)),
            Body::Join(a, b) => b.with_last(s, chars).map(|b| node(a.clone(), b)),
        }
    }

    /// `s`, of `chars` characters, added before the first block of `self`, when the two fit in
    /// one leaf.
    fn with_first(&self, s: &str, chars: usize) -> Option<Text> {
        match &self.0.body {
            Body::Leaf(first) => (s.len() + first.len() <= LEAF)
                .then(|| leaf([s, &**first].concat().into(), chars + self.0.chars)),
            Body::Join(a, b) => a.with_first(s, chars).map(|a| node(a, b.clone())),
        }
    }

    /// The two parts of a join.
    fn parts(&self) -> (&Text, &Text) {
        match &self.0.body {
            Body::Join(a, b) => (a, b),
            Body::Leaf(_) => unreachable!("a node of height above 0 is a join"),
        }
    }
}

/// A leaf holding `s`, of `chars` characters.
fn leaf(s: Arc<str>, chars: usize) -> Text {
    Text(Arc::new(Node {
        len: s.len(),
        chars,
        height: 0,
        body: Body::Leaf(s),
    }))
}

/// The join of `a` and `b`, whose heights differ by at most 1.
fn node(a: Text, b: Text) -> Text {
    debug_assert!(a.0.height.abs_diff(b.0.height) <= 1);
    Text(Arc::new(Node {
        // The caller checked that the whole text's length is representable; a part's is less.
        len: a.0.len + b.0.len,
        chars: a.0.chars + b.0.chars,
        height: a.0.height.max(b.0.height) + 1,
        body: Body::Join(a, b),
    }))
}

/// `a` then `b`, both balanced and not empty: the lower is joined into the side of the higher
/// that faces it, down to a part of about its height, and each node on the way back up is
/// rebalanced. `O(|height(a) - height(b)| + 1)` new nodes; the recursion is as deep, at most 92.
fn concat(a: &Text, b: &Text) -> Text {
    let (ha, hb) = (a.0.height, b.0.height);
    if ha > hb + 1 {
        let (l, r) = a.parts();
        balance(l.clone(), concat(r, b))
    } else if hb > ha + 1 {
        let (l, r) = b.parts();
        balance(concat(a, l), r.clone())
    } else {
        node(a.clone(), b.clone())
    }
}

/// The join of `l` and `r`, balanced trees whose heights differ by at most 2, rotated once or
/// twice when they differ by 2, as in an AVL tree.
fn balance(l: Text, r: Text) -> Text {
    let (hl, hr) = (l.0.height, r.0.height);
    debug_assert!(hl.abs_diff(hr) <= 2);
    if hl > hr + 1 {
        let (ll, lr) = l.parts();
        if ll.0.height >= lr.0.height {
            node(ll.clone(), node(lr.clone(), r))
        } else {
            let (lrl, lrr) = lr.parts();
            node(node(ll.clone(), lrl.clone()), node(lrr.clone(), r))
        }
    } else if hr > hl + 1 {
        let (rl, rr) = r.parts();
        if rr.0.height >= rl.0.height {
            node(node(l, rl.clone()), rr.clone())
        } else {
            let (rll, rlr) = rl.parts();
            node(node(l, rll.clone()), node(rlr.clone(), rr.clone()))
        }
    } else {
        node(l, r)
    }
}

/// The blocks of a text from left to right ([`Text::chunks`]).
pub struct Chunks<'a> {
    /// The parts still to read, the next on top; one per level at most, besides the top.
    todo: Vec<&'a Text>,
}

impl<'a> Iterator for Chunks<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        while let Some(t) = self.todo.pop() {
            match &t.0.body {
                Body::Leaf(s) if s.is_empty() => {}
                Body::Leaf(s) => return Some(s),
                Body::Join(a, b) => {
                    self.todo.push(b);
                    self.todo.push(a);
                }
            }
        }
        None
    }
}

/// The order of the bytes of `a` and `b`, read block by block until the first that differ.
fn compare(a: &Text, b: &Text) -> Ordering {
    let (mut xs, mut ys) = (a.chunks(), b.chunks());
    let (mut x, mut y): (&[u8], &[u8]) = (&[], &[]);
    loop {
        if x.is_empty() {
            match xs.next() {
                Some(s) => x = s.as_bytes(),
                None if y.is_empty() && ys.next().is_none() => return Ordering::Equal,
                None => return Ordering::Less,
            }
        }
        if y.is_empty() {
            match ys.next() {
                Some(s) => y = s.as_bytes(),
                None => return Ordering::Greater,
            }
        }
        let k = x.len().min(y.len());
        match x[..k].cmp(&y[..k]) {
            Ordering::Equal => (x, y) = (&x[k..], &y[k..]),
            other => return other,
        }
    }
}

impl From<Arc<str>> for Text {
    fn from(s: Arc<str>) -> Self {
        let chars = s.chars().count();
        leaf(s, chars)
    }
}

impl From<&str> for Text {
    fn from(s: &str) -> Self {
        Text::from(Arc::<str>::from(s))
    }
}

impl From<String> for Text {
    fn from(s: String) -> Self {
        Text::from(Arc::<str>::from(s))
    }
}

impl From<&String> for Text {
    fn from(s: &String) -> Self {
        Text::from(s.as_str())
    }
}

impl From<Text> for Arc<str> {
    /// A block shared, or a join written into a new block.
    fn from(t: Text) -> Self {
        match &t.0.body {
            Body::Leaf(s) => s.clone(),
            Body::Join(..) => t.flat().into(),
        }
    }
}

impl PartialEq for Text {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
            || (self.0.len == other.0.len
                && self.0.chars == other.0.chars
                && compare(self, other) == Ordering::Equal)
    }
}

impl Eq for Text {}

impl PartialOrd for Text {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Text {
    /// The order of `str`, by bytes, stopping at the first that differ.
    fn cmp(&self, other: &Self) -> Ordering {
        if Arc::ptr_eq(&self.0, &other.0) {
            return Ordering::Equal;
        }
        compare(self, other)
    }
}

/// The bytes a [`Text`] gives its hasher in each call but the last.
const BLOCK: usize = 64;

impl Hash for Text {
    /// The bytes go to the hasher in blocks of `BLOCK` bytes and a last shorter one, whatever
    /// the leaves, so equal texts hash alike however they were joined; then `0xff`, as a `str`
    /// ends its hash. A hasher that reads its input as one stream, as `DefaultHasher` does,
    /// so hashes a text as it hashes the same `str`.
    fn hash<H: Hasher>(&self, h: &mut H) {
        let mut buf = [0u8; BLOCK];
        let mut used = 0;
        for c in self.chunks() {
            let mut c = c.as_bytes();
            while !c.is_empty() {
                if used == 0 && c.len() >= BLOCK {
                    h.write(&c[..BLOCK]);
                    c = &c[BLOCK..];
                    continue;
                }
                let k = (BLOCK - used).min(c.len());
                buf[used..used + k].copy_from_slice(&c[..k]);
                (used, c) = (used + k, &c[k..]);
                if used == BLOCK {
                    h.write(&buf);
                    used = 0;
                }
            }
        }
        h.write(&buf[..used]);
        h.write_u8(0xff);
    }
}

impl fmt::Debug for Text {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&*self.flat(), f)
    }
}

impl fmt::Display for Text {
    /// The blocks in order; a width or a precision pads or cuts the text as a `str`'s does.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.width().is_some() || f.precision().is_some() {
            return f.pad(&self.flat());
        }
        self.chunks().try_for_each(|c| f.write_str(c))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Every expected text below is a literal or a plain `String` built by `push_str`, never
    // text the rope wrote out, so a fault in `join` or in reading shows as a difference.
    // `Text::len` is the kept count; `str::len` of `flat` is the length of the text read.

    /// The length of a test piece, in characters: two never share a block.
    const PIECE: usize = LEAF;

    fn long(c: char) -> Text {
        Text::from(c.to_string().repeat(PIECE))
    }

    fn join(a: &Text, b: &Text) -> Text {
        Text::join(a, b).unwrap()
    }

    /// The bytes of `t`, read by blocks.
    fn bytes(t: &Text) -> impl Iterator<Item = u8> + '_ {
        t.chunks().flat_map(str::bytes)
    }

    /// Panics unless every node of `t` is balanced and its counts are its parts': `O(len)`.
    fn assert_balanced(t: &Text) {
        let mut todo = vec![t];
        while let Some(t) = todo.pop() {
            match &t.0.body {
                Body::Leaf(s) => {
                    assert_eq!((t.0.height, t.0.len), (0, s.len()));
                    assert_eq!(t.0.chars, s.chars().count());
                }
                Body::Join(a, b) => {
                    assert!(a.0.len > 0 && b.0.len > 0, "a join of an empty part");
                    assert!(a.0.height.abs_diff(b.0.height) <= 1, "unbalanced");
                    assert_eq!(t.0.height, a.0.height.max(b.0.height) + 1);
                    assert_eq!(
                        (t.0.len, t.0.chars),
                        (a.0.len + b.0.len, a.0.chars + b.0.chars)
                    );
                    todo.extend([a, b]);
                }
            }
        }
    }

    /// The number of leaves of `t`, counting a shared one each time it is reached.
    fn leaves(t: &Text) -> usize {
        t.chunks().count()
    }

    #[test]
    fn a_join_reads_as_its_parts_in_order() {
        let (a, b) = (long('a'), long('b'));
        let ab = join(&a, &b);
        let mut want = "a".repeat(PIECE);
        want.push_str(&"b".repeat(PIECE));
        assert_eq!(ab.flat(), want);
        assert_eq!(ab.to_string(), want);
        assert_eq!(join(&Text::from(""), &a).flat(), "a".repeat(PIECE));
        assert_eq!(join(&Text::from("x"), &Text::from("y")).flat(), "xy");
        // Equal text, made two ways, is equal and orders the same.
        let whole = Text::from(want.clone());
        assert_eq!(ab, whole);
        assert_eq!(ab.cmp(&whole), Ordering::Equal);
        assert!(ab < join(&a, &long('c')));
        assert!(join(&a, &long('c')) > ab);
        // A text is less than a longer one it begins, whichever is joined.
        assert!(a < ab && ab > a);
        assert!(Text::from("") < a);
        // A width pads and a precision cuts the text as a `str`'s do.
        assert_eq!(format!("{ab:>300}"), format!("{want:>300}"));
        assert_eq!(format!("{ab:.3}|{ab:?}"), format!("{want:.3}|{want:?}"));
        assert_eq!(&*Arc::<str>::from(ab), want);
    }

    #[test]
    fn lengths_are_kept_through_joins() {
        // "naïve " is 6 characters in 7 bytes; "日本" 2 in 6; "" none.
        // Each piece is one `Text`, joined ten times, so the chain shares it.
        let pieces = ["naïve ", "", "日本", "a"];
        let parts = pieces.map(Text::from);
        let mut t = Text::from("");
        let mut want = String::new();
        for (p, part) in pieces.iter().zip(&parts).cycle().take(40) {
            t = join(&t, part);
            want.push_str(p);
        }
        assert_eq!((t.len(), t.char_count()), (140, 90));
        assert_eq!(t.flat(), want);
        assert_eq!((t.flat().len(), t.flat().chars().count()), (140, 90));
        assert_balanced(&t);
        // Two short strings joined are one block.
        let xy = join(&Text::from("x"), &Text::from("ÿ"));
        assert!(xy.is_flat());
        assert_eq!((xy.len(), xy.char_count(), &*xy.flat()), (3, 2, "xÿ"));
        // Two long ones are a join, read as one.
        let ab = join(&long('a'), &long('b'));
        assert!(!ab.is_flat());
        assert_eq!(ab.char_count(), 2 * PIECE);
    }

    #[test]
    fn a_string_joined_with_itself_reads_twice() {
        let s = join(&Text::from("tō"), &Text::from("kyō"));
        let ss = join(&s, &s);
        // "tōkyō" is 5 characters in 7 bytes.
        assert_eq!((ss.len(), ss.char_count()), (14, 10));
        assert_eq!(ss.flat(), "tōkyōtōkyō");
        let l = long('é');
        let ll = join(&join(&l, &l), &join(&l, &l));
        assert_eq!(ll.flat(), "é".repeat(4 * PIECE));
        assert_balanced(&ll);
        // The empty string joined with itself, any number of times, is the empty string.
        let mut e = Text::from("");
        for _ in 0..64 {
            e = join(&e, &e);
        }
        assert_eq!((e.len(), e.char_count(), &*e.flat()), (0, 0, ""));
        assert_eq!(e.chunks().count(), 0);
    }

    /// A block doubled `k` times, `s = s ++ s`: `2^k` blocks long.
    fn doubled(block: &str, k: u32) -> Result<Text, KernelError> {
        let mut s = Text::from(block);
        for _ in 0..k {
            s = Text::join(&s, &s)?;
        }
        Ok(s)
    }

    #[test]
    fn a_string_doubled_to_2_63_bytes_keeps_its_length() {
        for k in [62, 63] {
            let s = doubled("a", k).unwrap();
            assert_eq!((s.len(), s.char_count()), (1 << k, 1 << k));
            assert!(s.0.height <= 63);
        }
        // `ä` is one character in two bytes.
        let s = doubled("ä", 62).unwrap();
        assert_eq!((s.len(), s.char_count()), (1 << 63, 1 << 62));
        // Two such strings differing in their first byte compare at once.
        let t = join(&Text::from("b"), &doubled("a", 62).unwrap());
        assert!(join(&Text::from("a"), &doubled("a", 62).unwrap()) < t);
        assert_ne!(doubled("a", 62).unwrap(), doubled("b", 62).unwrap());
    }

    #[test]
    fn a_string_doubled_to_2_64_bytes_is_refused() {
        let half = 1usize << 63;
        let too_long = KernelError::StringTooLong {
            left: half,
            right: half,
        };
        assert_eq!(doubled("a", 64).unwrap_err(), too_long);
        assert_eq!(doubled("ä", 63).unwrap_err(), too_long);
        assert_eq!(
            too_long.to_string(),
            "`++` cannot join a string of 9223372036854775808 bytes to one of \
             9223372036854775808 bytes: the result would be 18446744073709551616 bytes, more \
             than the 18446744073709551615 bytes a string's length can hold; keep the parts \
             apart, as a list of strings written out one at a time, or join fewer of them"
        );
    }

    #[test]
    fn a_string_of_usize_max_bytes_is_kept_and_one_byte_more_is_refused() {
        // 1 + 2 + … + 2^63 = 2^64 - 1 bytes: the strings doubled 0 to 63 times, joined.
        let mut all = Text::from("");
        let mut s = Text::from("a");
        for k in 0..64 {
            all = join(&all, &s);
            if k < 63 {
                s = join(&s, &s);
            }
        }
        assert_eq!((all.len(), all.char_count()), (usize::MAX, usize::MAX));
        assert!(all.0.height <= 92, "the AVL bound for 2^64 leaves");
        assert_eq!(
            Text::join(&all, &Text::from("b")).unwrap_err(),
            KernelError::StringTooLong {
                left: usize::MAX,
                right: 1,
            }
        );
        // An empty string adds nothing, so it joins even here.
        assert_eq!(join(&all, &Text::from("")).len(), usize::MAX);
    }

    #[test]
    fn a_chain_a_million_long_either_way_is_balanced_read_and_dropped() {
        let piece = long('z');
        let n = 1_000_000;
        // `n` leaves: the AVL bound is `1.44 log2(n + 2)`, under 29.
        for left in [true, false] {
            let mut t = Text::from("");
            for _ in 0..n {
                t = if left {
                    join(&t, &piece)
                } else {
                    join(&piece, &t)
                };
            }
            assert_eq!((t.len(), t.char_count()), (PIECE * n, PIECE * n));
            assert!(t.0.height <= 29, "height {}", t.0.height);
            assert_eq!(leaves(&t), n);
            assert_eq!(t.flat().len(), PIECE * n, "every piece is read");
            assert!(bytes(&t).all(|b| b == b'z'));
            drop(t);
        }
    }

    #[test]
    fn joins_in_any_order_keep_the_tree_balanced_and_the_text_whole() {
        // Texts of 1 to 300 bytes, some of several characters' bytes, joined in an order a
        // fixed generator picks, each against a plain `String`.
        let mut seed = 0x9e37_79b9_7f4a_7c15_u64;
        let mut next = move |k: usize| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            (seed % k as u64) as usize
        };
        let mut pool: Vec<(Text, String)> = (1..=40)
            .map(|i| {
                let s = ["x", "ö", "日"][i % 3].repeat(1 + next(100));
                (Text::from(s.as_str()), s)
            })
            .collect();
        for _ in 0..2000 {
            let (i, j) = (next(pool.len()), next(pool.len()));
            if pool[i].1.len() + pool[j].1.len() > 1 << 15 {
                continue;
            }
            let t = join(&pool[i].0, &pool[j].0);
            let s = format!("{}{}", pool[i].1, pool[j].1);
            assert_balanced(&t);
            assert_eq!(t.flat(), s);
            assert_eq!(t, Text::from(s.as_str()));
            pool.push((t, s));
        }
        // Order and equality agree with `str`'s, on every pair of a sample.
        for (a, sa) in pool.iter().step_by(37) {
            for (b, sb) in pool.iter().step_by(41) {
                assert_eq!(a.cmp(b), sa.cmp(sb));
                assert_eq!(a == b, sa == sb);
            }
        }
    }

    #[test]
    fn equal_texts_hash_alike_however_joined() {
        use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
        let hash = |t: &dyn Fn(&mut DefaultHasher)| {
            let mut h = BuildHasherDefault::<DefaultHasher>::default().build_hasher();
            t(&mut h);
            h.finish()
        };
        // 1000 bytes in pieces of 7 and of 300, neither a multiple of the block given the hasher.
        let want: String = (0..1000)
            .map(|i| char::from(b'a' + (i % 26) as u8))
            .collect();
        let by = |k: usize| {
            want.as_bytes().chunks(k).fold(Text::from(""), |t, c| {
                join(&t, &Text::from(std::str::from_utf8(c).unwrap()))
            })
        };
        let (a, b) = (by(7), by(300));
        assert_eq!(a, b);
        let of = |t: &Text| hash(&|h| t.hash(h));
        assert_eq!(of(&a), of(&b));
        // `DefaultHasher` reads one stream, so a text hashes as its `str` does.
        assert_eq!(of(&a), hash(&|h| want.as_str().hash(h)));
        assert_ne!(of(&a), of(&by(7).flat().replace('a', "b").into()));
    }

    #[test]
    fn a_string_built_a_character_at_a_time_is_held_in_blocks() {
        let n = 10_000;
        let mut t = Text::from("");
        for i in 0..n {
            t = join(&t, &Text::from(if i % 2 == 0 { "x" } else { "ÿ" }));
        }
        assert_eq!((t.len(), t.char_count()), (3 * n / 2, n));
        // Each block but the last is filled to within one character of `LEAF` bytes.
        assert!(
            leaves(&t) <= t.len() / (LEAF - 1) + 1,
            "{} leaves",
            leaves(&t)
        );
        assert_balanced(&t);
        // The same, a character at a time to the front.
        let mut u = Text::from("");
        for _ in 0..n {
            u = join(&Text::from("q"), &u);
        }
        assert!(leaves(&u) <= n / LEAF + 1, "{} leaves", leaves(&u));
        assert_eq!(u.flat(), "q".repeat(n));
    }

    #[test]
    fn reading_every_prefix_costs_the_text_read() {
        // A log printed in full after every line: line `i` reads `i` lines, so `n` lines
        // read `n²/2` lines in all, and each read must cost in proportion to its length
        // (COMPLEXITY.md C29). The work is of order `n²`, so 8n may do 24 × 8 times that of n.
        let line = long('l');
        crate::scaling::check_order("a log of n lines printed after every line", 400, 2, |n| {
            let mut log = Text::from("");
            for i in 1..=n {
                log = join(&log, &line);
                let printed = bytes(&log).filter(|&b| b == b'l').count();
                assert_eq!(printed, PIECE * i);
            }
        });
    }

    #[test]
    fn reading_every_prefix_held_keeps_no_copy_of_it() {
        // A log of n lines whose every prefix is held, each printed, hashed and compared in
        // full: a read walks the blocks and keeps nothing, so all the reads together allocate
        // only each walk's stack, never the text (COMPLEXITY.md R5, C29). A read that wrote
        // the text out, kept or not, would allocate `n²/2` lines.
        use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
        use std::io::Write;
        let line = long('l');
        let n = 500;
        let mut log = Text::from("");
        let held: Vec<Text> = (0..n)
            .map(|_| {
                log = join(&log, &line);
                log.clone()
            })
            .collect();
        let mut sink = std::io::sink();
        let hasher = BuildHasherDefault::<DefaultHasher>::default();
        let before = zed_alloc_count::allocated();
        for t in &held {
            write!(sink, "{t}").unwrap();
            hasher.hash_one(t);
            assert!(*t <= log);
        }
        let read = zed_alloc_count::allocated() - before;
        // Four walks per prefix (print, hash, both sides of `<=`), each a stack of at most
        // the height plus one references.
        let stacks = 4 * n * (usize::from(log.0.height) + 1) * size_of::<&Text>();
        assert!(
            read <= stacks as u64,
            "{read} bytes allocated reading {} bytes of text, stacks {stacks}",
            n * (n + 1) / 2 * PIECE
        );
    }

    #[test]
    fn every_prefix_held_and_compared_costs_order_n_log_n() {
        // A log of n lines whose every prefix is kept, each compared, by `<` and by `==`, with
        // a log of the same length that differs in its first byte: each comparison stops
        // there, and each prefix shares all but `O(log n)` nodes with the one before
        // (COMPLEXITY.md C29). Order `n log n`, so 8n may do 24 times the work of n.
        let line = long('l');
        let first = join(&Text::from("m"), &Text::from("l".repeat(PIECE - 1)));
        crate::scaling::check("n prefixes of a log held and compared", 2000, |n| {
            let mut held = Vec::with_capacity(n);
            let (mut log, mut differs) = (Text::from(""), Text::from(""));
            for _ in 0..n {
                log = join(&log, &line);
                differs = if differs.is_empty() {
                    first.clone()
                } else {
                    join(&differs, &line)
                };
                assert!(log < differs && log != differs);
                held.push(log.clone());
            }
            assert_eq!(held.len(), n);
        });
    }

    #[test]
    fn a_chain_either_way_is_built_in_order_n_log_n() {
        let piece = long('p');
        for left in [true, false] {
            crate::scaling::check("a chain of n joins", 5000, |n| {
                let mut t = Text::from("");
                for _ in 0..n {
                    t = if left {
                        join(&t, &piece)
                    } else {
                        join(&piece, &t)
                    };
                }
                assert_eq!(t.len(), PIECE * n);
            });
        }
    }
}
