//! The text of a string value. A string joined by `++` is kept as the node of its two parts,
//! made in `O(1)`, and is written out once, when it is first read as text; a string is still
//! compared, ordered and printed by its text alone (DESIGN.md: "ropes are a representation and
//! never enter identity"). Joining `n` pieces one at a time, as a `foldl` of `++` does, so
//! costs `O(n)` and keeps `O(n)` memory for all its accumulators, where copying both parts at
//! each join cost `O(n²)` for both.

use std::cmp::Ordering;
use std::fmt;
use std::ops::Deref;
use std::sync::{Arc, OnceLock};

/// Joins whose text is at most this many bytes are written out at once.
const SHORT: usize = 64;

/// A string's text, shared.
#[derive(Clone)]
pub struct Text(Arc<Node>);

struct Node {
    /// The length of the text in bytes.
    len: usize,
    /// The text, once written out.
    flat: OnceLock<Arc<str>>,
    /// The two parts of a join; `None` for text made whole.
    parts: Option<(Text, Text)>,
}

impl Text {
    /// The text `a` then `b`.
    pub fn join(a: &Text, b: &Text) -> Text {
        if a.0.len == 0 {
            return b.clone();
        }
        if b.0.len == 0 {
            return a.clone();
        }
        let len = a.0.len + b.0.len;
        if len <= SHORT {
            return Text::from(format!("{}{}", &**a, &**b));
        }
        Text(Arc::new(Node {
            len,
            flat: OnceLock::new(),
            parts: Some((a.clone(), b.clone())),
        }))
    }

    /// The text written out: the parts of a join from left to right, each part already written
    /// out read whole. The walk keeps its own stack, so a join nested a million deep is safe.
    fn write_out(&self) -> Arc<str> {
        let mut out = String::with_capacity(self.0.len);
        let mut todo = vec![self];
        while let Some(t) = todo.pop() {
            match (t.0.flat.get(), &t.0.parts) {
                (Some(s), _) => out.push_str(s),
                (None, Some((a, b))) => {
                    todo.push(b);
                    todo.push(a);
                }
                (None, None) => unreachable!("text made whole is written out when made"),
            }
        }
        out.into()
    }
}

impl Drop for Node {
    /// Drops a chain of joins one node at a time, not by a recursion as deep as the chain.
    fn drop(&mut self) {
        let mut todo: Vec<Text> = match self.parts.take() {
            Some((a, b)) => vec![a, b],
            None => return,
        };
        while let Some(t) = todo.pop() {
            if let Ok(mut node) = Arc::try_unwrap(t.0)
                && let Some((a, b)) = node.parts.take()
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
        self.0.flat.get_or_init(|| self.write_out())
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
            flat: OnceLock::from(s),
            parts: None,
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

    fn long(c: char) -> Text {
        Text::from(c.to_string().repeat(SHORT))
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
    fn a_chain_a_million_deep_is_written_out_and_dropped() {
        let piece = long('z');
        let mut t = Text::from("");
        for _ in 0..1_000_000 {
            t = Text::join(&t, &piece);
        }
        assert_eq!(t.len(), SHORT * 1_000_000);
        assert!(t.bytes().all(|b| b == b'z'));
        drop(t);
    }
}
