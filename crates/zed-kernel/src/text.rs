//! The text of a string value, for the kernel and the native runtime alike. A string joined by
//! `++` is kept as the node of its two parts, made in `O(1)`, and is written out once, when it
//! is first read as text; a string is still compared, ordered and printed by its text alone
//! (DESIGN.md: "ropes are a representation and never enter identity"). Joining `n` pieces one
//! at a time, as a `foldl` of `++` does, so costs `O(n)` and keeps `O(n)` memory for all its
//! accumulators, where copying both parts at each join cost `O(n²)` for both.
//!
//! Each node keeps its length in bytes and in characters, counted when text is made whole and
//! added when two are joined, so `len` is `O(1)` and never writes the text out (COMPLEXITY.md
//! R4, R5). The tree is not balanced: every walk over it, writing out and dropping, keeps its
//! own stack, so its depth is the length of a chain of joins and costs no machine stack.
//!
//! A node written out lets go of its two parts, so it holds only its own text. Reading every
//! step of a chain of joins, the accumulator each time, so holds the latest text only, not
//! one copy per step, `O(n²)` bytes in all.

use std::cmp::Ordering;
use std::fmt;
use std::ops::Deref;
use std::sync::{Arc, Mutex, OnceLock, PoisonError};

/// A string's text, shared.
#[derive(Clone)]
pub struct Text(Arc<Node>);

struct Node {
    /// The length of the text in bytes.
    len: usize,
    /// The length of the text in characters (Unicode scalar values), what `len` gives.
    chars: usize,
    /// The text, once written out.
    flat: OnceLock<Arc<str>>,
    /// The two parts of a join; `None` for text made whole and for a join once written out.
    parts: Mutex<Option<(Text, Text)>>,
}

impl Node {
    /// The two parts of a join not yet written out, shared.
    fn parts(&self) -> Option<(Text, Text)> {
        self.parts
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }
}

impl Text {
    /// The text `a` then `b`, in `O(1)`: neither part is copied or read.
    pub fn join(a: &Text, b: &Text) -> Text {
        if a.0.len == 0 {
            return b.clone();
        }
        if b.0.len == 0 {
            return a.clone();
        }
        Text(Arc::new(Node {
            len: a.0.len + b.0.len,
            chars: a.0.chars + b.0.chars,
            flat: OnceLock::new(),
            parts: Mutex::new(Some((a.clone(), b.clone()))),
        }))
    }

    /// The length in bytes, without writing the text out.
    pub fn len(&self) -> usize {
        self.0.len
    }

    /// Whether the text is empty.
    pub fn is_empty(&self) -> bool {
        self.0.len == 0
    }

    /// The number of characters, Unicode scalar values, without writing the text out.
    pub fn char_count(&self) -> usize {
        self.0.chars
    }

    /// Whether the text is written out already, so reading it copies nothing.
    pub fn is_written_out(&self) -> bool {
        self.0.flat.get().is_some()
    }

    /// The text written out: the parts of a join from left to right, each part already written
    /// out read whole. The walk keeps its own stack, so a join nested a million deep is safe.
    fn write_out(&self) -> Arc<str> {
        let mut out = String::with_capacity(self.0.len);
        let mut todo = vec![self.clone()];
        while let Some(t) = todo.pop() {
            if let Some(s) = t.0.flat.get() {
                out.push_str(s);
            } else if let Some((a, b)) = t.0.parts() {
                todo.push(b);
                todo.push(a);
            } else {
                // Another thread wrote this part out and let go of its parts since `flat` was
                // read above; its text is there now.
                let s = t.0.flat.get();
                out.push_str(s.expect("a node lets go of its parts only once written out"));
            }
        }
        out.into()
    }
}

impl Drop for Node {
    /// Drops a chain of joins one node at a time, not by a recursion as deep as the chain.
    fn drop(&mut self) {
        let parts = self.parts.get_mut().unwrap_or_else(PoisonError::into_inner);
        let mut todo: Vec<Text> = match parts.take() {
            Some((a, b)) => vec![a, b],
            None => return,
        };
        while let Some(t) = todo.pop() {
            if let Ok(mut node) = Arc::try_unwrap(t.0)
                && let Some((a, b)) = node
                    .parts
                    .get_mut()
                    .unwrap_or_else(PoisonError::into_inner)
                    .take()
            {
                todo.push(a);
                todo.push(b);
            }
        }
    }
}

impl Deref for Text {
    type Target = str;
    fn deref(&self) -> &str {
        if let Some(s) = self.0.flat.get() {
            return s;
        }
        let s = self.0.flat.get_or_init(|| self.write_out());
        // The text is in `flat` now, so the parts are not read again; once let go of, a part
        // nothing else holds is freed.
        let parts = self
            .0
            .parts
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .take();
        drop(parts);
        s
    }
}

impl AsRef<str> for Text {
    fn as_ref(&self) -> &str {
        self
    }
}

impl From<Arc<str>> for Text {
    fn from(s: Arc<str>) -> Self {
        Text(Arc::new(Node {
            len: s.len(),
            chars: s.chars().count(),
            flat: OnceLock::from(s),
            parts: Mutex::new(None),
        }))
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
    fn from(t: Text) -> Self {
        let _ = &*t;
        t.0.flat.get().expect("written out above").clone()
    }
}

impl PartialEq for Text {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || (self.0.len == other.0.len && **self == **other)
    }
}

impl Eq for Text {}

impl PartialOrd for Text {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Text {
    fn cmp(&self, other: &Self) -> Ordering {
        (**self).cmp(&**other)
    }
}

impl std::hash::Hash for Text {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        (**self).hash(h)
    }
}

impl fmt::Debug for Text {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl fmt::Display for Text {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The length of a test piece, in characters.
    const PIECE: usize = 64;

    fn long(c: char) -> Text {
        Text::from(c.to_string().repeat(PIECE))
    }

    #[test]
    fn a_join_reads_as_its_parts_in_order() {
        let (a, b) = (long('a'), long('b'));
        let ab = Text::join(&a, &b);
        assert_eq!(&*ab, format!("{a}{b}"));
        assert_eq!(Text::join(&Text::from(""), &a), a);
        assert_eq!(
            Text::join(&Text::from("x"), &Text::from("y")),
            Text::from("xy")
        );
        // Equal text, made two ways, is equal and orders the same.
        let whole = Text::from(format!("{a}{b}"));
        assert_eq!(ab, whole);
        assert_eq!(ab.cmp(&whole), Ordering::Equal);
        assert!(ab < Text::join(&a, &long('c')));
    }

    #[test]
    fn lengths_are_kept_through_joins_without_writing_out() {
        // "naïve " is 6 characters in 7 bytes; "日本" 2 in 6; "" none.
        let parts = ["naïve ", "", "日本", "a"].map(Text::from);
        for p in &parts {
            assert_eq!(p.char_count(), p.chars().count());
        }
        let mut t = Text::from("");
        for p in parts.iter().cycle().take(40) {
            t = Text::join(&t, p);
        }
        assert_eq!((t.len(), t.char_count()), (140, 90));
        assert!(!t.is_written_out(), "neither length reads the text");
        assert_eq!(t.char_count(), t.chars().count());
        assert!(t.is_written_out());
        // Two short strings joined are a node too; they read as one.
        let xy = Text::join(&Text::from("x"), &Text::from("ÿ"));
        assert!(!xy.is_written_out());
        assert_eq!((xy.len(), xy.char_count(), &*xy), (3, 2, "xÿ"));
    }

    #[test]
    fn a_chain_a_million_deep_is_written_out_and_dropped() {
        let piece = long('z');
        let mut t = Text::from("");
        for _ in 0..1_000_000 {
            t = Text::join(&t, &piece);
        }
        assert_eq!(t.len(), PIECE * 1_000_000);
        assert_eq!(t.char_count(), PIECE * 1_000_000);
        assert!(t.bytes().all(|b| b == b'z'));
        drop(t);
        // A chain never read keeps all its nodes, and drops them one at a time.
        let mut t = Text::from("");
        for _ in 0..1_000_000 {
            t = Text::join(&t, &piece);
        }
        assert!(!t.is_written_out());
        drop(t);
    }

    #[test]
    fn a_log_read_after_every_line_keeps_only_its_latest_text() {
        // An accumulator read at every step, as a log printed line by line is: each step,
        // once read, holds its own text and not the step before, so the steps not held
        // elsewhere are freed and memory stays that of the latest text.
        let line = long('l');
        let mut log = Text::from("log:");
        for i in 1..=100 {
            let before = log.clone();
            log = Text::join(&log, &line);
            assert_eq!(log.len(), 4 + PIECE * i);
            assert!(log.ends_with(&*line));
            assert!(log.0.parts().is_none(), "the parts are let go of once read");
            assert_eq!(
                Arc::strong_count(&before.0),
                1,
                "only this test holds the step before"
            );
        }
    }
}
