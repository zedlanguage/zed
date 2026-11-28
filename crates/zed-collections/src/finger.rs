//! A persistent, strict 2-3 finger tree of leaves, each node keeping the measure of its leaves
//! added, and the deque and join operations on it: the tree of a string's blocks (zed-kernel
//! `text.rs`, `Text`) and of the lists a list made by `++` joins (zed-kernel `value.rs`,
//! `Chain`), written once (plan row DRY-persistent-trees-2026-11-26, step 11).
//!
//! Source. R. Hinze and R. Paterson, "Finger trees: a simple general-purpose data structure",
//! Journal of Functional Programming 16(2), 197-217, 2006 (online 2005),
//! doi:10.1017/S0956796805005769. What is taken, in the paper's terms and this module's:
//! - section 3.1: `Deep` holds a prefix digit, a middle finger tree of `Node`s, and a suffix
//!   digit, "allowing between one and four subtrees at each level" ([`Shape::Deep`], [`Digit`]);
//!   level `n` holds 2-3 trees of depth `n` ([`Shape::Node`], parts of two or three);
//! - section 3.2: the deque operations `◁` and `▷` ([`push_front`], [`push_back`]): a push onto
//!   a digit of four moves three into the middle as a `Node3`; digits of two or three are
//!   "safe", of one or four "dangerous", and only a dangerous digit carries to the next level,
//!   so "at most half of the operations descend one level, at most a quarter two levels";
//! - section 3.3: concatenation `app3 xs ts ys`, which joins the inner digits and the list
//!   between them into nodes with `nodes` and recurses on the middles ([`concat()`], `nodes`,
//!   the same grouping: two parts or four as `Node2`s, otherwise `Node3`s first), "the total
//!   time taken is Θ(log(min{n1, n2}))";
//! - section 4.2: each node caches its measure, a monoid ([`Leaf::Measure`]).
//!
//! Departure: the paper's `O(1)` amortized bound holds "even in a persistent setting" because
//! the middle of each `Deep` is suspended by lazy evaluation (section 3.2, the debit argument).
//! The tree here is strict, so the bound holds for a chain of joins each made on the last
//! result, not for pushes repeated onto one old version (the tradeoff comment at
//! [`push_back`]). Checked 2026-11-19 against the paper's text (the publisher's PDF, sections
//! 3.1-3.3 and 4.2) and its Crossref metadata, when this code was first written in zed-kernel
//! `text.rs`.
//!
//! A tree of `b` leaves is at most `log2(b/2 + 1)` levels deep: the deep tree at level `k`
//! holds parts of height `k`, one to four in each digit ([`digit`] asserts it, and the
//! operations here only build digits of one to four), so two or more; a part of height `k` is a
//! leaf (`k = 0`) or a node of two or three parts of height `k - 1` ([`node`] asserts it), so by
//! induction it holds `2^k` leaves or more, and `b >= 2 (1 + 2 + ... + 2^(d-1)) = 2 (2^d - 1)`.
//! The users bound `b` (a block holds a byte or more of at most `usize::MAX`; a leaf holds an
//! entry or more of at most `i64::MAX`), so every recursion here is under 64 levels deep.
//!
//! The parts of a node are the user's own handle ([`Leaf::Part`], a newtype over [`Tree`]), so
//! a node of a string's tree holds `Text`s and a reader of the string walks `Text`s, with no
//! conversion. Tested by the users: zed-kernel `text::tests::assert_balanced` (every digit one
//! to four parts, every node two or three, every level its parts' height, every cached measure
//! their sum), `a_chain_of_joins_allocates_a_constant_per_join` for the amortized bound, and
//! `value::tests::lists_joined_in_any_shape_are_equal_and_read_alike`.

use std::fmt::Debug;
use std::ops::{Add, Deref};
use std::sync::Arc;

/// A leaf of a finger tree, with the measure each node keeps and the handle its parts are.
pub trait Leaf: Sized {
    /// The measure of a leaf, added over the leaves of a part (section 4.2's monoid, with
    /// `Default` its zero).
    type Measure: Copy + Default + Add<Output = Self::Measure> + PartialEq + Debug;
    /// What each node and deep tree keeps besides its measure, made empty (`Default`) when the
    /// node is made: a cell its user fills on a read; `()` for none.
    type Cache: Default;
    /// The handle of a part, a newtype over [`Tree`]; the parts of each node are handles.
    type Part: Clone;
    /// The measure of this leaf.
    fn measure(&self) -> Self::Measure;
    /// The tree a handle holds.
    fn tree(part: &Self::Part) -> &Tree<Self>;
    /// The handle of a tree.
    fn part(tree: Tree<Self>) -> Self::Part;
}

/// A finger tree, or a part of one, shared. It dereferences to its [`Shape`].
pub struct Tree<L: Leaf>(Arc<Shape<L>>);

// Every function here is `#[inline]`. Without it a generic function's copy for one leaf type
// sits in one codegen unit of the user's crate, and with `lto = "off"` (Cargo.toml) the user's
// other units call it out of line: the port of zed-kernel's string tree to this module, without
// it, took 2.5-16.7% more instructions on text benches whose loops read a node per step
// (`a compare of two trees of n blocks` +16.7%). `#[inline]` copies each into every unit that
// calls it, as the private functions in `text.rs` were before.
impl<L: Leaf> Clone for Tree<L> {
    #[inline]
    fn clone(&self) -> Self {
        Tree(self.0.clone())
    }
}

impl<L: Leaf> Deref for Tree<L> {
    type Target = Shape<L>;

    #[inline]
    fn deref(&self) -> &Shape<L> {
        &self.0
    }
}

/// One to four parts of one height, in order, the first `Some` and no `Some` after a `None`.
pub type Digit<L> = [Option<<L as Leaf>::Part>; 4];

/// What a [`Tree`] is.
pub enum Shape<L: Leaf> {
    /// The empty tree, and the middle of a deep tree that has nothing between its ends.
    Empty,
    /// A leaf: a part of height 0.
    Leaf(L),
    /// Two or three parts of one height `h`, in order, the third `None` when there are two, and
    /// their measure: a part of height `h + 1`.
    Node {
        /// The measure of its parts, added.
        measure: L::Measure,
        /// Its parts in order, the third `None` when there are two.
        parts: [Option<L::Part>; 3],
        /// Its user's cell ([`Leaf::Cache`]).
        cache: L::Cache,
    },
    /// A tree of parts of height `h`: `front`, then the parts of the nodes of height `h + 1`
    /// that `middle` holds, then `back`, and their measure. A tree of one part is that part
    /// itself.
    Deep {
        /// The measure of its ends and middle, added.
        measure: L::Measure,
        /// The first one to four parts.
        front: Digit<L>,
        /// The tree of the nodes between the ends, one height up.
        middle: L::Part,
        /// The last one to four parts.
        back: Digit<L>,
        /// Its user's cell ([`Leaf::Cache`]).
        cache: L::Cache,
    },
}

impl<L: Leaf> Tree<L> {
    /// The address of this tree's node, which names it while any handle to it lives.
    #[inline]
    pub fn addr(&self) -> usize {
        Arc::as_ptr(&self.0).addr()
    }

    /// Whether the two are one node.
    #[inline]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }

    /// The measure of its leaves. O(1).
    #[inline]
    pub fn measure(&self) -> L::Measure {
        match &*self.0 {
            Shape::Empty => L::Measure::default(),
            Shape::Leaf(l) => l.measure(),
            Shape::Node { measure, .. } | Shape::Deep { measure, .. } => *measure,
        }
    }

    /// The number of deep trees from this one down its middles: `O(log n)`.
    #[inline]
    pub fn depth(&self) -> usize {
        let (mut d, mut t) = (0, self);
        while let Shape::Deep { middle, .. } = &*t.0 {
            (d, t) = (d + 1, L::tree(middle));
        }
        d
    }

    /// The parts beneath this one, in order, the middle of a deep tree among them.
    #[inline]
    pub fn parts(&self) -> impl DoubleEndedIterator<Item = &L::Part> {
        let (a, middle, b): (&[_], _, &[_]) = match &*self.0 {
            Shape::Empty | Shape::Leaf(_) => (&[], None, &[]),
            Shape::Node { parts, .. } => (parts.as_slice(), None, &[]),
            Shape::Deep {
                front,
                middle,
                back,
                ..
            } => (front.as_slice(), Some(middle), back.as_slice()),
        };
        a.iter().flatten().chain(middle).chain(b.iter().flatten())
    }
}

/// The measure of a part.
#[inline]
fn measure<L: Leaf>(p: &L::Part) -> L::Measure {
    L::tree(p).measure()
}

/// The handle of a new node of the given shape.
#[inline]
fn made<L: Leaf>(shape: Shape<L>) -> L::Part {
    L::part(Tree(Arc::new(shape)))
}

/// The empty tree.
#[inline]
pub fn empty<L: Leaf>() -> L::Part {
    made::<L>(Shape::Empty)
}

/// The part of height 0 that is the leaf `l`.
#[inline]
pub fn leaf<L: Leaf>(l: L) -> L::Part {
    made(Shape::Leaf(l))
}

/// The number of parts of a digit.
#[inline]
pub fn count<T>(d: &[Option<T>; 4]) -> usize {
    d.iter().take_while(|p| p.is_some()).count()
}

/// A digit of the given parts, one to four.
#[inline]
pub fn digit<L: Leaf>(parts: &[L::Part]) -> Digit<L> {
    debug_assert!((1..=4).contains(&parts.len()));
    std::array::from_fn(|i| parts.get(i).cloned())
}

/// The node of two or three parts of one height.
#[inline]
pub fn node<L: Leaf>(parts: &[L::Part]) -> L::Part {
    debug_assert!((2..=3).contains(&parts.len()));
    let measure = parts
        .iter()
        .map(measure::<L>)
        .fold(L::Measure::default(), Add::add);
    let parts = std::array::from_fn(|i| parts.get(i).cloned());
    made::<L>(Shape::Node {
        measure,
        parts,
        cache: L::Cache::default(),
    })
}

/// The deep tree of the given ends and middle, whose measures add up to `measure`: the callers
/// know it from the tree they extend, so a push reads no part but the one it adds.
#[inline]
pub fn deep<L: Leaf>(
    measure: L::Measure,
    front: Digit<L>,
    middle: L::Part,
    back: Digit<L>,
) -> L::Part {
    debug_assert_eq!(
        measure,
        front
            .iter()
            .chain(&back)
            .flatten()
            .map(self::measure::<L>)
            .fold(self::measure::<L>(&middle), Add::add)
    );
    made::<L>(Shape::Deep {
        measure,
        front,
        middle,
        back,
        cache: L::Cache::default(),
    })
}

// Complexity tradeoff: `push_back` and `push_front` are strict, so their `O(1)` is amortized
// over a sequence of pushes each made on the result of the one before, as a `foldl` of `++`
// makes them: a push onto a full end (four parts) moves three of them into the middle as a
// node and leaves two, so the next two pushes at that end cannot carry. Given up: a program
// that keeps one tree whose ends are full at every level and pushes onto that same tree again
// and again pays `O(depth)` = `O(log n)` new nodes for each of those pushes, the cost of the
// AVL tree the string's tree replaced; the result is the same. Why: an `O(1)` bound that holds
// under any reuse of an old version needs the middle suspended and forced later (Hinze and
// Paterson's lazy middle) or the regular digits of Kaplan and Tarjan's catenable deques, a cell
// written after the node is shared or several times the code here. (H. Kaplan and R. E.
// Tarjan, "Purely functional, real-time deques with catenation", J. ACM 46(5), 577-603, 1999,
// doi:10.1145/324133.324139: "worst-case running time of O(1) for each push, pop, inject,
// eject and catenation", from "redundant digital representations used to avoid carry
// propagation in binary counting"; checked 2026-11-19 against the abstract and Crossref, the
// structure itself not read, since it is not used here.) Trigger: pushes onto one version
// whose ends are full down its middles. Test: zed-kernel
// `text::tests::a_chain_of_joins_allocates_a_constant_per_join` (the chain), and
// `joins_in_any_order_keep_the_tree_balanced_and_the_text_whole` (any reuse);
// COMPLEXITY.md C29.
/// `t` then the part `p`, of the height of `t`'s parts.
#[inline]
pub fn push_back<L: Leaf>(t: &L::Part, p: L::Part) -> L::Part {
    let m = measure::<L>(t) + measure::<L>(&p);
    match &**L::tree(t) {
        Shape::Empty => p,
        Shape::Leaf(_) | Shape::Node { .. } => deep::<L>(
            m,
            digit::<L>(std::slice::from_ref(t)),
            empty::<L>(),
            digit::<L>(&[p]),
        ),
        Shape::Deep {
            front,
            middle,
            back,
            ..
        } => match back {
            [Some(a), Some(b), Some(c), Some(d)] => deep::<L>(
                m,
                front.clone(),
                push_back::<L>(middle, node::<L>(&[a.clone(), b.clone(), c.clone()])),
                digit::<L>(&[d.clone(), p]),
            ),
            _ => {
                let mut back = back.clone();
                back[count(&back)] = Some(p);
                deep::<L>(m, front.clone(), middle.clone(), back)
            }
        },
    }
}

/// The part `p` then `t`, `p` of the height of `t`'s parts.
#[inline]
pub fn push_front<L: Leaf>(p: L::Part, t: &L::Part) -> L::Part {
    let m = measure::<L>(&p) + measure::<L>(t);
    match &**L::tree(t) {
        Shape::Empty => p,
        Shape::Leaf(_) | Shape::Node { .. } => deep::<L>(
            m,
            digit::<L>(&[p]),
            empty::<L>(),
            digit::<L>(std::slice::from_ref(t)),
        ),
        Shape::Deep {
            front,
            middle,
            back,
            ..
        } => match front {
            [Some(a), Some(b), Some(c), Some(d)] => deep::<L>(
                m,
                digit::<L>(&[p, a.clone()]),
                push_front::<L>(node::<L>(&[b.clone(), c.clone(), d.clone()]), middle),
                back.clone(),
            ),
            [a, b, c, _] => deep::<L>(
                m,
                [Some(p), a.clone(), b.clone(), c.clone()],
                middle.clone(),
                back.clone(),
            ),
        },
    }
}

/// `a`, the parts `between`, then `b`: trees of parts of one height, and at most four parts
/// between. One level of the recursion per level of the shallower tree, each building `O(1)`
/// nodes, so `O(log m)` in all, `m` the number of leaves of the shorter; the recursion is that
/// deep, under 64.
#[inline]
pub fn concat<L: Leaf>(a: &L::Part, between: &[L::Part], b: &L::Part) -> L::Part {
    let onto_b = || {
        between
            .iter()
            .rev()
            .fold(b.clone(), |t, p| push_front::<L>(p.clone(), &t))
    };
    let onto_a = || {
        between
            .iter()
            .fold(a.clone(), |t, p| push_back::<L>(&t, p.clone()))
    };
    match (&**L::tree(a), &**L::tree(b)) {
        (Shape::Empty, _) => onto_b(),
        (_, Shape::Empty) => onto_a(),
        (Shape::Leaf(_) | Shape::Node { .. }, _) => push_front::<L>(a.clone(), &onto_b()),
        (_, Shape::Leaf(_) | Shape::Node { .. }) => push_back::<L>(&onto_a(), b.clone()),
        (
            Shape::Deep {
                front,
                middle: m1,
                back: b1,
                ..
            },
            Shape::Deep {
                front: f2,
                middle: m2,
                back,
                ..
            },
        ) => {
            let parts: Vec<L::Part> = b1
                .iter()
                .flatten()
                .chain(between)
                .chain(f2.iter().flatten())
                .cloned()
                .collect();
            let m = between
                .iter()
                .map(measure::<L>)
                .fold(measure::<L>(a), Add::add)
                + measure::<L>(b);
            deep::<L>(
                m,
                front.clone(),
                concat::<L>(m1, &nodes::<L>(&parts), m2),
                back.clone(),
            )
        }
    }
}

/// Two to twelve parts of one height as nodes of two or three, in order: at most four.
///
/// Proof. `concat` gives it the parts of one back digit, `between` and one front digit: one
/// to four, at most four (the nodes of the level above, by this bound), one to four, so two
/// to twelve. The loop takes two parts when two or four are left and three otherwise, so
/// from five or more it leaves two or more, from three it leaves none, and one part is never
/// left alone: every node has two or three parts. Twelve parts make four nodes of three, and
/// fewer parts no more nodes, so `concat`'s `between` is at most four parts at every level.
#[inline]
fn nodes<L: Leaf>(mut parts: &[L::Part]) -> Vec<L::Part> {
    let mut out = Vec::with_capacity(parts.len().div_ceil(3));
    while !parts.is_empty() {
        let k = if matches!(parts.len(), 2 | 4) { 2 } else { 3 };
        out.push(node::<L>(&parts[..k]));
        parts = &parts[k..];
    }
    out
}

/// The tree `t`, whose top parts are leaves (a leaf, or a deep tree with leaves in its
/// digits), with its last leaf replaced by `merge` of it, when `merge` gives one; `added` is
/// the new leaf's measure less the old one's. `O(1)` nodes made: the leaf and the deep tree at
/// the top.
#[inline]
pub fn with_last<L: Leaf>(
    t: &L::Part,
    added: L::Measure,
    merge: impl FnOnce(&L) -> Option<L>,
) -> Option<L::Part> {
    match &**L::tree(t) {
        Shape::Leaf(l) => merge(l).map(leaf::<L>),
        Shape::Deep {
            measure,
            front,
            middle,
            back,
            ..
        } => {
            let i = count(back) - 1;
            let last = with_last::<L>(back[i].as_ref()?, added, merge)?;
            let mut back = back.clone();
            back[i] = Some(last);
            Some(deep::<L>(
                *measure + added,
                front.clone(),
                middle.clone(),
                back,
            ))
        }
        // A tree whose top parts are leaves is never empty and never a node.
        Shape::Empty | Shape::Node { .. } => None,
    }
}

/// The tree `t`, as for [`with_last`], with its first leaf replaced by `merge` of it.
#[inline]
pub fn with_first<L: Leaf>(
    t: &L::Part,
    added: L::Measure,
    merge: impl FnOnce(&L) -> Option<L>,
) -> Option<L::Part> {
    match &**L::tree(t) {
        Shape::Leaf(l) => merge(l).map(leaf::<L>),
        Shape::Deep {
            measure,
            front,
            middle,
            back,
            ..
        } => {
            let first = with_first::<L>(front[0].as_ref()?, added, merge)?;
            let mut front = front.clone();
            front[0] = Some(first);
            Some(deep::<L>(
                *measure + added,
                front,
                middle.clone(),
                back.clone(),
            ))
        }
        Shape::Empty | Shape::Node { .. } => None,
    }
}
