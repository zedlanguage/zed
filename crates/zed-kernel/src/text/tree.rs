//! The representation of a string's text ([`Text`]): the finger tree of blocks that the
//! parent module `text` builds, reads and joins, and that `names` summarizes. The types are
//! here, apart from their methods in `text.rs`, so that both files import this one and neither
//! imports the other.

use std::ops::Add;
use std::sync::Arc;

/// A string's text, shared.
#[derive(Clone)]
pub struct Text(pub(super) Arc<Tree>);

/// A length in bytes and in characters (Unicode scalar values).
// Complexity tradeoff: the naive `len` counts the characters of the text at each call
// (`s.chars().count()`), O(n) per call, O(n²) for a loop that reads the length of a growing
// string (COMPLEXITY.md R4: 39.1 to 63.9 times for 8 times the size). Here each tree and node
// keeps its length in bytes and in characters, counted once when a block is made and added at
// a join, so `len` and `char_count` are O(1) and read no text. Tradeoff: two words more per
// node, and one character count per block made. Nothing is refused. Tests
// `l01_36_cranelift::string_scaling` and `l01_36_cranelift::strings`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub(super) struct Size {
    pub(super) len: usize,
    pub(super) chars: usize,
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
pub(super) type Digit = [Option<Text>; 4];

pub(super) enum Tree {
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
