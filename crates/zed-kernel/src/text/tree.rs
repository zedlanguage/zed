//! The representation of a string's text ([`Text`]): the finger tree of blocks that the
//! parent module `text` builds, reads and joins, and that `names` summarizes. The types are
//! here, apart from their methods in `text.rs`, so that both files import this one and neither
//! imports the other. The tree and its operations are zed-collections' [`finger`] tree, whose
//! leaves here are blocks ([`Block`]) measured by their [`Size`].

use std::ops::Add;
use std::sync::Arc;

use zed_collections::finger::{self, Leaf};

/// A string's text, shared.
#[derive(Clone)]
pub struct Text(pub(super) finger::Tree<Block>);

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
pub(super) type Digit = finger::Digit<Block>;

/// What a text's tree is ([`finger::Shape`]): `Empty` (the empty text, and the middle of a deep
/// tree that has nothing between its ends), `Leaf` (a [`Block`], a part of height 0), `Node`
/// (two or three parts of one height and their size) or `Deep` (`front`, the nodes `middle`
/// holds, then `back`, and their size).
pub(super) type Tree = finger::Shape<Block>;

/// A block of text, not empty, and its number of characters: a leaf of a text's tree.
pub(super) struct Block {
    pub(super) block: Arc<str>,
    pub(super) chars: usize,
}

impl Leaf for Block {
    type Measure = Size;
    type Cache = ();
    type Part = Text;

    // `#[inline]`, as every function of `finger` is (its comment at `Clone for Tree`): these
    // run at every node a read or a push of a text visits.
    #[inline]
    fn measure(&self) -> Size {
        Size {
            len: self.block.len(),
            chars: self.chars,
        }
    }

    #[inline]
    fn tree(part: &Text) -> &finger::Tree<Block> {
        &part.0
    }

    #[inline]
    fn part(tree: finger::Tree<Block>) -> Text {
        Text(tree)
    }
}
