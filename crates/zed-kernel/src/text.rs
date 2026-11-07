//! The text of a string value, for the kernel and the native runtime alike. A string joined by
//! `++` is kept as a tree whose leaves are blocks of text, and a string is still compared,
//! ordered and printed by its text alone (DESIGN.md: "ropes are a representation and never
//! enter identity").
//!
//! The tree is a finger tree of blocks (Hinze and Paterson, "Finger trees: a simple
//! general-purpose data structure", JFP 16(2), 2006), persistent and shared: a deep tree keeps
//! one to four parts at each end and a tree of nodes of two or three parts between them, whose
//! parts are one level higher. A join that adds a block at either end builds `O(1)` new nodes,
//! amortized over a chain of joins each made on the result of the one before, as a `foldl` of
//! `++` makes them (DESIGN.md: `++` is O(1)); a join of two longer texts builds `O(log m)`, `m`
//! the number of blocks of the shorter. Holding every prefix of a chain of `n` joins keeps
//! `O(n)` nodes (COMPLEXITY.md C29).
//!
//! Every tree, node and block is itself a [`Text`], whose blocks in order are its text: a text
//! held as one block is the part a join puts in a tree, with nothing added. A tree of `b`
//! blocks is at most `log2(b/2 + 1)` levels deep (each level holds two parts or more, and a
//! part at level `k` holds `2^k` blocks or more), so at most 63, and every walk over it, reading
//! or dropping, keeps that bound.
//!
//! Nothing is written out and kept: readers walk the blocks in order ([`Text::chunks`]), so a
//! comparison stops at the first byte that differs, in `O(log n)` plus the bytes it reads;
//! hashing and printing cost the text's length. A reader that needs the text as one `&str`
//! gets it from [`Text::flat`], which borrows a single block and writes a join into a new
//! `String` at each call.
//!
//! Each tree and node keeps its length in bytes and in characters, added when it is built, so
//! `len` is `O(1)` and reads no text (COMPLEXITY.md R4, R5).

use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Add;
use std::sync::Arc;

use num_bigint::BigUint;

use crate::KernelError;
use crate::num::TooLarge;

/// A string's text, shared.
#[derive(Clone)]
pub struct Text(Arc<Tree>);

/// A length in bytes and in characters (Unicode scalar values).
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
struct Size {
    len: usize,
    chars: usize,
}

impl Add for Size {
    type Output = Size;

    /// The size of two parts of one text: the join that made the text checked that its length
    /// in bytes is representable, and it has no more characters than bytes.
    fn add(self, other: Size) -> Size {
        Size {
            len: self.len + other.len,
            chars: self.chars + other.chars,
        }
    }
}

/// One to four parts of one height, in order, the first `Some` and no `Some` after a `None`.
type Digit = [Option<Text>; 4];

enum Tree {
    /// The empty text, and the middle of a deep tree that has nothing between its ends.
    Empty,
    /// A block of text, not empty, and its number of characters: a part of height 0.
    Block { block: Arc<str>, chars: usize },
    /// Two or three parts of one height `h`, in order, the third `None` when there are two: a
    /// part of height `h + 1`.
    Node {
        size: Size,
        parts: [Option<Text>; 3],
    },
    /// A tree of parts of height `h`: `front`, then the parts of the nodes of height `h + 1`
    /// that `middle` holds, then `back`. A tree of one part is that part itself.
    Deep {
        size: Size,
        front: Digit,
        middle: Text,
        back: Digit,
    },
}

// Complexity tradeoff: a join of two texts whose bytes fit in `LEAF` together, or of a short
// text to the end block of a longer one, copies them into one block of at most `LEAF` bytes,
// `O(LEAF)` work and memory per join. Cost: a join that would otherwise only share its parts
// copies up to `LEAF` bytes, so `n` prefixes held keep up to `LEAF` bytes each besides their
// `O(1)` nodes. Given up: nothing in order; the result and every reader are the same. Why:
// a string built a character at a time would otherwise hold a node of about 112 bytes and a
// block of 16 bytes of counts for each character, and every read would walk that many blocks.
// Measured (WRITE-prefix-scale merge, on the AVL tree this tree replaced, release, load 62 to
// 69, a `foldl` of 200,000 joins of one piece, merging on against off): 1-byte pieces, 1,563
// leaves of height 11 against 200,000 of height 18, `==` of two such texts 0.2 ms against 34
// to 40 ms, a hash 0.3 to 3.6 ms against 22 to 24 ms, printing 0.3 to 1.3 ms against 18 to 23
// ms; 8-byte pieces, `==` 2 to 5 ms against 11 to 39 ms; 128-byte pieces, which never merge,
// the same. One more effect: a join of at most `LEAF` bytes is one block ([`Text::is_flat`]),
// so staging keys a call at it by its answers (`zedc::stage::compared`) and a call at a longer
// join by the function's term; the value is the same either way. Trigger: a join whose parts'
// adjacent blocks are short. Test:
// `text::tests::a_string_built_a_character_at_a_time_is_held_in_blocks`; COMPLEXITY.md C29. A
// solution with no constant would need blocks whose size follows the text's own pieces with
// no node per piece, which no structure here has.
const LEAF: usize = 128;

impl Text {
    /// The text `a` then `b`. A join shares both parts; it builds `O(1)` new nodes, amortized,
    /// when either is one block, as a `foldl` of `++` joins, and `O(log m)` for two longer
    /// texts, `m` the number of blocks of the shorter; it copies no more than `LEAF` bytes. A
    /// join shares its parts, so a string doubled 64 times is a few thousand nodes and `2^64`
    /// times as long as the first: when the two lengths in bytes add up past `usize::MAX` the
    /// join's length is not representable, and it is refused with
    /// [`KernelError::StringTooLong`].
    pub fn join(a: &Text, b: &Text) -> Result<Text, KernelError> {
        if a.is_empty() {
            return Ok(b.clone());
        }
        if b.is_empty() {
            return Ok(a.clone());
        }
        if a.len().checked_add(b.len()).is_none() {
            return Err(KernelError::StringTooLong {
                left: a.len(),
                right: b.len(),
            });
        }
        if let Tree::Block { block, chars } = &*b.0
            && let Some(t) = a.with_last(block, *chars)
        {
            return Ok(t);
        }
        if let Tree::Block { block, chars } = &*a.0
            && let Some(t) = b.with_first(block, *chars)
        {
            return Ok(t);
        }
        Ok(concat(a, &[], b))
    }

    /// The length in bytes, without reading the text.
    pub fn len(&self) -> usize {
        self.size().len
    }

    /// Whether the text is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The number of characters, Unicode scalar values, without reading the text.
    pub fn char_count(&self) -> usize {
        self.size().chars
    }

    /// Whether the text is held as one block, so [`Text::flat`] copies nothing and a reader
    /// walks no tree: a join, of any length, is held in parts and never written out.
    pub fn is_flat(&self) -> bool {
        matches!(*self.0, Tree::Empty | Tree::Block { .. })
    }

    /// The blocks of the text from left to right, none empty. The walk keeps its own stack,
    /// of at most `6d + 9` parts for a tree `d` levels deep, allocated once: `O(log n)` for
    /// the first block, and every block in `O(len)`.
    pub fn chunks(&self) -> Chunks<'_> {
        let mut todo = Vec::with_capacity(6 * self.depth() + 9);
        todo.push(self);
        Chunks { todo }
    }

    /// The text as one `&str`: a text held as one block is borrowed; a join is written into a
    /// new `String` at each call, `O(len)`, and not kept, so holding a text never holds a
    /// second copy of it. For readers that need one `&str`, as `lower` and a cast do.
    pub fn flat(&self) -> Cow<'_, str> {
        match &*self.0 {
            Tree::Empty => Cow::Borrowed(""),
            Tree::Block { block, .. } => Cow::Borrowed(block),
            Tree::Node { .. } | Tree::Deep { .. } => {
                let mut out = String::with_capacity(self.len());
                self.chunks().for_each(|c| out.push_str(c));
                Cow::Owned(out)
            }
        }
    }

    /// The text as one `&str`, as [`Text::flat`] gives it, with a join written into memory the
    /// system gives first for all of it; [`TooLarge`] when it refuses, naming that memory, so
    /// a reader of a text too long to copy, as a cast is, reports it and does not abort.
    pub fn try_flat(&self) -> Result<Cow<'_, str>, TooLarge> {
        match &*self.0 {
            Tree::Empty => Ok(Cow::Borrowed("")),
            Tree::Block { block, .. } => Ok(Cow::Borrowed(block)),
            Tree::Node { .. } | Tree::Deep { .. } => {
                let mut out = String::new();
                out.try_reserve_exact(self.len()).map_err(|_| TooLarge {
                    bits: BigUint::from(self.len()) << 3u32,
                })?;
                self.chunks().for_each(|c| out.push_str(c));
                Ok(Cow::Owned(out))
            }
        }
    }

    fn size(&self) -> Size {
        match &*self.0 {
            Tree::Empty => Size::default(),
            Tree::Block { block, chars } => Size {
                len: block.len(),
                chars: *chars,
            },
            Tree::Node { size, .. } | Tree::Deep { size, .. } => *size,
        }
    }

    /// The number of deep trees from this one down its middles: `O(log n)`.
    fn depth(&self) -> usize {
        let (mut d, mut t) = (0, self);
        while let Tree::Deep { middle, .. } = &*t.0 {
            (d, t) = (d + 1, middle);
        }
        d
    }

    /// `self`, a text's tree, with `s`, of `chars` characters, added to its last block, when
    /// the two fit in one block: `O(LEAF)`, the deep tree at the top rebuilt.
    fn with_last(&self, s: &str, chars: usize) -> Option<Text> {
        match &*self.0 {
            Tree::Block { block, chars: c } => (block.len() + s.len() <= LEAF)
                .then(|| block_of([&**block, s].concat().into(), c + chars)),
            Tree::Deep {
                front,
                middle,
                back,
                ..
            } => {
                let i = count(back) - 1;
                let last = back[i].as_ref()?.with_last(s, chars)?;
                let mut back = back.clone();
                back[i] = Some(last);
                Some(deep(
                    self.size()
                        + Size {
                            len: s.len(),
                            chars,
                        },
                    front.clone(),
                    middle.clone(),
                    back,
                ))
            }
            // A text's own tree holds blocks at the top, never a node.
            Tree::Empty | Tree::Node { .. } => None,
        }
    }

    /// `s`, of `chars` characters, added before the first block of `self`, a text's tree, when
    /// the two fit in one block.
    fn with_first(&self, s: &str, chars: usize) -> Option<Text> {
        match &*self.0 {
            Tree::Block { block, chars: c } => (s.len() + block.len() <= LEAF)
                .then(|| block_of([s, &**block].concat().into(), chars + c)),
            Tree::Deep {
                front,
                middle,
                back,
                ..
            } => {
                let first = front[0].as_ref()?.with_first(s, chars)?;
                let mut front = front.clone();
                front[0] = Some(first);
                Some(deep(
                    self.size()
                        + Size {
                            len: s.len(),
                            chars,
                        },
                    front,
                    middle.clone(),
                    back.clone(),
                ))
            }
            Tree::Empty | Tree::Node { .. } => None,
        }
    }
}

/// A block holding `s`, not empty, of `chars` characters.
fn block_of(block: Arc<str>, chars: usize) -> Text {
    Text(Arc::new(Tree::Block { block, chars }))
}

fn empty() -> Text {
    Text(Arc::new(Tree::Empty))
}

/// The number of parts of a digit.
fn count(d: &Digit) -> usize {
    d.iter().take_while(|p| p.is_some()).count()
}

/// A digit of the given parts, one to four.
fn digit(parts: &[Text]) -> Digit {
    debug_assert!((1..=4).contains(&parts.len()));
    std::array::from_fn(|i| parts.get(i).cloned())
}

/// The node of two or three parts of one height.
fn node(parts: &[Text]) -> Text {
    debug_assert!((2..=3).contains(&parts.len()));
    let size = parts.iter().map(Text::size).fold(Size::default(), Add::add);
    let parts = std::array::from_fn(|i| parts.get(i).cloned());
    Text(Arc::new(Tree::Node { size, parts }))
}

/// The deep tree of the given ends and middle, whose sizes add up to `size`: the callers know
/// it from the tree they extend, so a push reads no part but the one it adds.
fn deep(size: Size, front: Digit, middle: Text, back: Digit) -> Text {
    debug_assert_eq!(
        size,
        front
            .iter()
            .chain(&back)
            .flatten()
            .map(Text::size)
            .fold(middle.size(), Add::add)
    );
    Text(Arc::new(Tree::Deep {
        size,
        front,
        middle,
        back,
    }))
}

// Complexity tradeoff: `push_back` and `push_front` are strict, so their `O(1)` is amortized
// over a sequence of pushes each made on the result of the one before, as a `foldl` of `++`
// makes them: a push onto a full end (four parts) moves three of them into the middle as a
// node and leaves two, so the next two pushes at that end cannot carry. Given up: a program
// that keeps one tree whose ends are full at every level and pushes onto that same tree again
// and again pays `O(depth)` = `O(log n)` new nodes for each of those pushes, the cost of the
// AVL tree this replaced; the text is the same. Why: an `O(1)` bound that holds under any
// reuse of an old version needs the middle suspended and forced later (Hinze and Paterson's
// lazy middle) or the regular digits of Kaplan and Tarjan's catenable deques, a cell written
// after the node is shared or several times the code here. Trigger: pushes onto one version
// whose ends are full down its middles. Test: `text::tests::a_chain_of_joins_allocates_a_
// constant_per_join` (the chain), and `joins_in_any_order_keep_the_tree_balanced_and_the_
// text_whole` (any reuse, the text); COMPLEXITY.md C29.
/// `t` then the part `p`, of the height of `t`'s parts.
fn push_back(t: &Text, p: Text) -> Text {
    let size = t.size() + p.size();
    match &*t.0 {
        Tree::Empty => p,
        Tree::Block { .. } | Tree::Node { .. } => {
            deep(size, digit(std::slice::from_ref(t)), empty(), digit(&[p]))
        }
        Tree::Deep {
            front,
            middle,
            back,
            ..
        } => match back {
            [Some(a), Some(b), Some(c), Some(d)] => deep(
                size,
                front.clone(),
                push_back(middle, node(&[a.clone(), b.clone(), c.clone()])),
                digit(&[d.clone(), p]),
            ),
            _ => {
                let mut back = back.clone();
                back[count(&back)] = Some(p);
                deep(size, front.clone(), middle.clone(), back)
            }
        },
    }
}

/// The part `p` then `t`, `p` of the height of `t`'s parts.
fn push_front(p: Text, t: &Text) -> Text {
    let size = p.size() + t.size();
    match &*t.0 {
        Tree::Empty => p,
        Tree::Block { .. } | Tree::Node { .. } => {
            deep(size, digit(&[p]), empty(), digit(std::slice::from_ref(t)))
        }
        Tree::Deep {
            front,
            middle,
            back,
            ..
        } => match front {
            [Some(a), Some(b), Some(c), Some(d)] => deep(
                size,
                digit(&[p, a.clone()]),
                push_front(node(&[b.clone(), c.clone(), d.clone()]), middle),
                back.clone(),
            ),
            [a, b, c, _] => deep(
                size,
                [Some(p), a.clone(), b.clone(), c.clone()],
                middle.clone(),
                back.clone(),
            ),
        },
    }
}

/// `a`, the parts `between`, then `b`: trees of parts of one height, and at most four parts
/// between. One level of the recursion per level of the shallower tree, each building `O(1)`
/// nodes, so `O(log m)` in all, `m` the number of blocks of the shorter; the recursion is that
/// deep, at most 63.
fn concat(a: &Text, between: &[Text], b: &Text) -> Text {
    match (&*a.0, &*b.0) {
        (Tree::Empty, _) => between
            .iter()
            .rev()
            .fold(b.clone(), |t, p| push_front(p.clone(), &t)),
        (_, Tree::Empty) => between
            .iter()
            .fold(a.clone(), |t, p| push_back(&t, p.clone())),
        (Tree::Block { .. } | Tree::Node { .. }, _) => {
            let t = between
                .iter()
                .rev()
                .fold(b.clone(), |t, p| push_front(p.clone(), &t));
            push_front(a.clone(), &t)
        }
        (_, Tree::Block { .. } | Tree::Node { .. }) => {
            let t = between
                .iter()
                .fold(a.clone(), |t, p| push_back(&t, p.clone()));
            push_back(&t, b.clone())
        }
        (
            Tree::Deep {
                front,
                middle: m1,
                back: b1,
                ..
            },
            Tree::Deep {
                front: f2,
                middle: m2,
                back,
                ..
            },
        ) => {
            let parts: Vec<Text> = b1
                .iter()
                .flatten()
                .chain(between)
                .chain(f2.iter().flatten())
                .cloned()
                .collect();
            let size = between.iter().map(Text::size).fold(a.size(), Add::add) + b.size();
            deep(
                size,
                front.clone(),
                concat(m1, &nodes(&parts), m2),
                back.clone(),
            )
        }
    }
}

/// Two to twelve parts of one height as nodes of two or three, in order: at most four.
fn nodes(mut parts: &[Text]) -> Vec<Text> {
    let mut out = Vec::with_capacity(parts.len().div_ceil(3));
    while !parts.is_empty() {
        let k = if matches!(parts.len(), 2 | 4) { 2 } else { 3 };
        out.push(node(&parts[..k]));
        parts = &parts[k..];
    }
    out
}

/// The blocks of a text from left to right ([`Text::chunks`]).
pub struct Chunks<'a> {
    /// The trees and parts still to read, the next on top.
    todo: Vec<&'a Text>,
}

impl<'a> Iterator for Chunks<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        while let Some(t) = self.todo.pop() {
            match &*t.0 {
                Tree::Empty => {}
                Tree::Block { block, .. } => return Some(block),
                Tree::Node { parts, .. } => self.todo.extend(parts.iter().rev().flatten()),
                Tree::Deep {
                    front,
                    middle,
                    back,
                    ..
                } => {
                    self.todo.extend(back.iter().rev().flatten());
                    self.todo.push(middle);
                    self.todo.extend(front.iter().rev().flatten());
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
        if s.is_empty() {
            return empty();
        }
        let chars = s.chars().count();
        block_of(s, chars)
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
        match &*t.0 {
            Tree::Block { block, .. } => block.clone(),
            Tree::Empty | Tree::Node { .. } | Tree::Deep { .. } => t.flat().into(),
        }
    }
}

impl PartialEq for Text {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
            || (self.size() == other.size() && compare(self, other) == Ordering::Equal)
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

    /// Panics unless `t` is a well-formed text tree: every digit holds one to four parts, every
    /// node two or three, every part at a level of the height of that level, no block empty,
    /// and every count its parts': `O(len)`.
    fn assert_balanced(t: &Text) {
        // A tree whose parts are of height `h` (`true`), or a part of height `h` (`false`).
        let mut todo = vec![(t, 0usize, true)];
        while let Some((t, h, tree)) = todo.pop() {
            match &*t.0 {
                Tree::Empty => assert!(tree, "an empty part"),
                Tree::Block { block, chars } => {
                    assert_eq!(h, 0, "a block among parts of height {h}");
                    assert!(!block.is_empty(), "an empty block");
                    assert_eq!(*chars, block.chars().count());
                }
                Tree::Node { size, parts } => {
                    assert!(h > 0, "a node among blocks");
                    assert!(
                        parts[0].is_some() && parts[1].is_some(),
                        "a node of one part"
                    );
                    let parts: Vec<&Text> = parts.iter().flatten().collect();
                    let sum = parts
                        .iter()
                        .map(|p| p.size())
                        .fold(Size::default(), Add::add);
                    assert_eq!(*size, sum);
                    todo.extend(parts.into_iter().map(|p| (p, h - 1, false)));
                }
                Tree::Deep {
                    size,
                    front,
                    middle,
                    back,
                } => {
                    assert!(tree, "a deep tree as a part");
                    for d in [front, back] {
                        let k = count(d);
                        assert!((1..=4).contains(&k), "a digit of {k} parts");
                        assert!(d[k..].iter().all(Option::is_none), "a gap in a digit");
                    }
                    let ends: Vec<&Text> = front.iter().chain(back).flatten().collect();
                    let sum = ends.iter().map(|p| p.size()).fold(middle.size(), Add::add);
                    assert_eq!(*size, sum);
                    todo.extend(ends.into_iter().map(|p| (p, h, false)));
                    todo.push((middle, h + 1, true));
                }
            }
        }
    }

    /// The bound on the depth of a tree of `b` blocks: `log2(b/2 + 1)`, rounded down.
    fn depth_bound(b: usize) -> usize {
        (b / 2 + 1).ilog2() as usize
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
            // Blocks of `LEAF` = 2^7 bytes, shared: 2^(k - 7) of them.
            assert!(
                s.depth() <= depth_bound(1 << (k - 7)),
                "depth {}",
                s.depth()
            );
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
        assert!(
            all.depth() <= depth_bound(usize::MAX),
            "depth {}",
            all.depth()
        );
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
        // `n` blocks: at most `log2(n/2 + 1)` levels, 18.
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
            assert!(t.depth() <= depth_bound(n), "depth {}", t.depth());
            assert_balanced(&t);
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
            // The walk never needs more than the stack `chunks` allocates.
            let mut walk = t.chunks();
            let stack = walk.todo.capacity();
            walk.by_ref().for_each(drop);
            assert_eq!(walk.todo.capacity(), stack, "the walk's stack grew");
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
        // `6d + 9` references for a tree `d` levels deep.
        let stacks = 4 * n * (6 * log.depth() + 9) * size_of::<&Text>();
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
        // there after setting up a walk of `O(log n)`, and each prefix shares all but `O(1)`
        // nodes, amortized, with the one before (COMPLEXITY.md C29). Order `n log n`, so 8n
        // may do 24 times the work of n.
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
    fn a_chain_of_joins_allocates_a_constant_per_join() {
        // A join at an end builds one deep tree, and every third join at that end carries a
        // node and a deep tree to the level below, every ninth one level further, and so on:
        // `1 + 2 (1/3 + 1/9 + …) = 2` trees per join, amortized, whatever `n`, and one empty
        // middle for each level made (COMPLEXITY.md C29). The AVL tree it replaced built
        // `O(log n)` nodes per join, about 17 at the larger size here.
        let piece = long('p');
        // A tree in its `Arc`, with the two counts.
        let tree = (size_of::<Tree>() + 2 * size_of::<usize>()) as u64;
        for n in [1 << 10, 1 << 17] {
            for left in [true, false] {
                let before = zed_alloc_count::allocated();
                let mut t = Text::from("");
                for _ in 0..n {
                    t = if left {
                        join(&t, &piece)
                    } else {
                        join(&piece, &t)
                    };
                }
                let bytes = zed_alloc_count::allocated() - before;
                assert_eq!(t.len(), PIECE * n);
                let most = (2 * n as u64 + 64) * tree;
                assert!(
                    bytes <= most,
                    "{n} joins, left {left}: {bytes} bytes, {} per join, more than {most}",
                    bytes / n as u64
                );
            }
        }
    }

    #[test]
    fn a_chain_either_way_is_built_in_order_n() {
        // The `foldl` of `++` of plan row TEXT-append-O1: order `n`, so 8n may do 24 times the
        // work of n.
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

    /// A text of `n` pieces, each a different character, joined one at a time at the end
    /// (`left`) or at the front, and the same text built by `push_str`.
    fn chain(n: usize, left: bool) -> (Text, String) {
        // One, two, three and four bytes a character, so a block boundary falls between
        // characters of every width.
        let chars = ['a', 'é', '日', '😀', 'z'];
        let (mut t, mut pieces) = (Text::from(""), Vec::with_capacity(n));
        for i in 0..n {
            let piece = chars[i % chars.len()].to_string().repeat(PIECE);
            let p = Text::from(piece.as_str());
            t = if left { join(&t, &p) } else { join(&p, &t) };
            pieces.push(piece);
        }
        if !left {
            pieces.reverse();
        }
        (t, pieces.concat())
    }

    #[test]
    fn try_flat_reads_every_shape_of_a_text_whole() {
        // The empty text and one block are borrowed, not copied.
        assert!(matches!(Text::from("").try_flat(), Ok(Cow::Borrowed(""))));
        let a = long('a');
        let Ok(Cow::Borrowed(s)) = a.try_flat() else {
            panic!("a text of one block is borrowed")
        };
        assert_eq!(s, "a".repeat(PIECE));
        // Two blocks; a block at each end and one between; then trees whose middles hold
        // nodes, and nodes of nodes, joined at either end.
        for n in [2, 3, 5, 9, 40, 1000] {
            for left in [true, false] {
                let (t, want) = chain(n, left);
                assert!(!t.is_flat());
                let Ok(Cow::Owned(got)) = t.try_flat() else {
                    panic!("a join of {n} blocks is written out")
                };
                assert_eq!(got, want, "{n} blocks, joined at the end {left}");
                // The memory asked for first holds all of it: the copy never grows.
                assert_eq!(got.capacity(), want.len());
                assert_eq!(got, t.flat());
            }
        }
        let (deep, _) = chain(1000, true);
        assert!(deep.depth() >= 3, "depth {}", deep.depth());
        // Two trees joined to each other, their inner ends' parts carried into the middle.
        let ((l, lw), (r, rw)) = (chain(40, true), chain(41, false));
        assert_eq!(join(&l, &r).try_flat().unwrap(), lw + &rw);
        // A tree shared with itself reads twice.
        let (s, sw) = chain(9, true);
        assert_eq!(join(&s, &s).try_flat().unwrap(), sw.repeat(2));
        // Short text merged into the end blocks of a join.
        let (t, tw) = chain(3, true);
        let ends = join(&join(&Text::from("-"), &t), &Text::from("."));
        assert_eq!(ends.try_flat().unwrap(), format!("-{tw}."));
    }

    #[test]
    fn try_flat_refuses_a_text_too_long_to_copy() {
        // 2^63 bytes is more than any allocation may ask for; 2^62 more than the address
        // space holds. Either is refused with the memory asked for, in bits.
        for k in [62, 63] {
            let s = doubled("a", k).unwrap();
            assert_eq!(
                s.try_flat().unwrap_err(),
                TooLarge {
                    bits: BigUint::from(1usize << k) << 3u32
                }
            );
        }
    }

    #[test]
    fn try_flat_of_a_join_costs_its_length() {
        // One walk over the blocks into memory asked for once: order `n` in the blocks, so 8n
        // may do 24 times the work of n. The texts are built before the runs are timed.
        let texts = crate::scaling::inputs(2000, |n| chain(n, true).0);
        crate::scaling::check("try_flat of a join of n blocks", 2000, |n| {
            let flat = texts[&n].try_flat().unwrap();
            assert_eq!(flat.chars().count(), PIECE * n);
        });
    }
}
