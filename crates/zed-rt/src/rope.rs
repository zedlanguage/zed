//! A rope-backed `String` (step L1.36): concatenation shares both sides and copies nothing,
//! and a rope is flattened to one buffer, once, when a primitive needs its text.

use std::sync::{Arc, OnceLock};

/// An immutable string as a tree of shared pieces.
#[derive(Clone, Debug)]
pub struct Rope(Arc<Node>);

#[derive(Debug)]
enum Node {
    Leaf(Arc<str>),
    Cat {
        left: Rope,
        right: Rope,
        bytes: usize,
        chars: usize,
        flat: OnceLock<Arc<str>>,
    },
}

impl Rope {
    /// The rope of one piece.
    pub fn leaf(s: Arc<str>) -> Rope {
        Rope(Arc::new(Node::Leaf(s)))
    }

    /// `a` followed by `b`, in constant time: neither side is copied.
    pub fn cat(a: &Rope, b: &Rope) -> Rope {
        if a.bytes() == 0 {
            return b.clone();
        }
        if b.bytes() == 0 {
            return a.clone();
        }
        Rope(Arc::new(Node::Cat {
            bytes: a.bytes() + b.bytes(),
            chars: a.chars() + b.chars(),
            left: a.clone(),
            right: b.clone(),
            flat: OnceLock::new(),
        }))
    }

    /// The length in bytes.
    pub fn bytes(&self) -> usize {
        match &*self.0 {
            Node::Leaf(s) => s.len(),
            Node::Cat { bytes, .. } => *bytes,
        }
    }

    /// The length in characters, what `len` gives.
    pub fn chars(&self) -> usize {
        match &*self.0 {
            Node::Leaf(s) => s.chars().count(),
            Node::Cat { chars, .. } => *chars,
        }
    }

    /// The text as one buffer. A piece is returned as it is; a concatenation is copied into
    /// one buffer the first time it is asked for, adding its length to `copied`, and kept.
    pub fn flat(&self, copied: &mut u64) -> Arc<str> {
        match &*self.0 {
            Node::Leaf(s) => s.clone(),
            Node::Cat { bytes, flat, .. } => flat
                .get_or_init(|| {
                    let mut out = String::with_capacity(*bytes);
                    // Iteratively, so a long chain of concatenations does not overflow the
                    // stack; a piece already flattened is copied whole.
                    let mut todo = vec![self];
                    while let Some(r) = todo.pop() {
                        match &*r.0 {
                            Node::Leaf(s) => out.push_str(s),
                            Node::Cat { flat, .. } if flat.get().is_some() => {
                                out.push_str(flat.get().expect("checked"))
                            }
                            Node::Cat { left, right, .. } => {
                                todo.push(right);
                                todo.push(left);
                            }
                        }
                    }
                    *copied += out.len() as u64;
                    out.into()
                })
                .clone(),
        }
    }
}

impl Drop for Rope {
    // A long chain of concatenations is dropped iteratively, for the same reason: each
    // node this rope holds alone gives up its sides to a list instead of dropping them.
    fn drop(&mut self) {
        let mut todo = Vec::new();
        take_sides(&mut self.0, &mut todo);
        while let Some(mut r) = todo.pop() {
            take_sides(&mut r.0, &mut todo);
        }
    }
}

fn take_sides(n: &mut Arc<Node>, todo: &mut Vec<Rope>) {
    static EMPTY: OnceLock<Arc<Node>> = OnceLock::new();
    let empty = || {
        Rope(
            EMPTY
                .get_or_init(|| Arc::new(Node::Leaf("".into())))
                .clone(),
        )
    };
    if let Some(Node::Cat { left, right, .. }) = Arc::get_mut(n) {
        todo.push(std::mem::replace(left, empty()));
        todo.push(std::mem::replace(right, empty()));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn concatenation_copies_once() {
        let mut r = Rope::leaf("".into());
        for i in 0..1000 {
            r = Rope::cat(&r, &Rope::leaf(format!("{i},").into()));
        }
        let mut copied = 0;
        let s = r.flat(&mut copied);
        assert_eq!(copied, s.len() as u64);
        assert_eq!(r.chars(), s.chars().count());
        assert!(s.starts_with("0,1,2,") && s.ends_with("999,"));
        r.flat(&mut copied);
        assert_eq!(copied, s.len() as u64, "a second flattening copies nothing");
    }

    #[test]
    fn a_long_chain_drops_without_overflow() {
        let mut r = Rope::leaf("x".into());
        for _ in 0..200_000 {
            r = Rope::cat(&Rope::leaf("y".into()), &r);
        }
        assert_eq!(r.bytes(), 200_001);
        drop(r);
    }
}
