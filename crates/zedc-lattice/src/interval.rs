//! The interval domain: finite unions of integer intervals with infinite endpoints (DESIGN.md
//! sec:constraints, "Intervals"; widening fixed by step M0.5).
//!
//! An element is a sorted list of disjoint pieces, each `lo..=hi`, with at least one integer
//! missing between two pieces, so that every set has exactly one representation and equality
//! of elements is equality of sets. The empty list is the empty set, the bottom of the lattice.
//! Meet and join are exact.
//!
//! An end is an unbounded integer ([`Num`]): one machine word while it fits in `i64`, a
//! `BigInt` past it. No end is rounded or dropped at any magnitude, since `int` is unbounded.

use std::cmp::Ordering;
use std::fmt;
use std::ops::Neg;
use std::sync::{Arc, OnceLock};

use zed_kernel::{Prim, Value};

use super::landmarks::Landmarks;
pub use zedc_int::int::Num;

/// An endpoint: an integer or one of the two infinities.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum End {
    /// Below every integer.
    NegInf,
    /// An integer.
    Fin(Num),
    /// Above every integer.
    PosInf,
}

use End::{Fin, NegInf, PosInf};

impl From<i64> for End {
    fn from(v: i64) -> End {
        Fin(Num::from(v))
    }
}

impl From<i128> for End {
    fn from(v: i128) -> End {
        Fin(Num::from(v))
    }
}

impl End {
    /// The integer `v`.
    pub fn of(v: i64) -> End {
        Fin(Num::from(v))
    }

    /// The integer, when the end is finite and fits in `i64`.
    pub fn to_i64(&self) -> Option<i64> {
        match self {
            Fin(v) => v.to_i64(),
            _ => None,
        }
    }

    /// The next integer up; the infinities are fixed.
    pub fn succ(&self) -> End {
        match self {
            Fin(v) => Fin(v + &Num::ONE),
            e => e.clone(),
        }
    }

    /// Whether `self <= other.succ()`, without expanding a kept power ([`Num::at_most_succ`]).
    pub fn at_most_succ(&self, other: &End) -> bool {
        match (self, other) {
            (Fin(a), Fin(b)) => a.at_most_succ(b),
            _ => *self <= other.succ(),
        }
    }

    /// The next integer down; the infinities are fixed.
    pub fn pred(&self) -> End {
        match self {
            Fin(v) => Fin(v - &Num::ONE),
            e => e.clone(),
        }
    }

    /// The sign: -1, 0 or 1.
    pub fn signum(&self) -> i8 {
        match self {
            NegInf => -1,
            PosInf => 1,
            Fin(v) => v.signum(),
        }
    }
}

impl Neg for &End {
    type Output = End;
    /// The negation, which swaps the infinities.
    fn neg(self) -> End {
        match self {
            NegInf => PosInf,
            PosInf => NegInf,
            Fin(v) => Fin(-v),
        }
    }
}

impl Neg for End {
    type Output = End;
    fn neg(self) -> End {
        -&self
    }
}

impl fmt::Display for End {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NegInf => write!(f, "-inf"),
            PosInf => write!(f, "inf"),
            Fin(v) => write!(f, "{v}"),
        }
    }
}

/// A finite union of integer intervals.
///
/// The pieces are kept in a persistent balanced search tree ordered by their lower ends (an
/// AVL tree joined and split as in Blelloch, Ferizovic and Sun, "Just Join for Parallel Ordered
/// Sets", 2016). A clone shares the whole tree; an operation that builds a new set copies only
/// the `O(log p)` nodes on the paths it changes and shares the rest. Each node also holds, for
/// its subtree, the count of pieces, the first and last ends and a hash of the pieces in
/// order, so that these are read in `O(1)`, and, once asked for, the longest run of integers
/// left out between two pieces.
// Complexity tradeoff: the naive version is a sorted `Vec` of pieces; there a membership test
// or a search is O(log p), but a clone, a meet, a join, an equality test and the longest gap
// are each O(p), so a scope that tests and narrows a name of p pieces once for each of n
// facts does O(n p) work: in the laps family of `l01_39_reduced_product` the meets and the
// longest gap grew as n^1.7 to n^2, and the family took 17.4 times the work for 8 times the
// names. Used: the persistent tree. A clone is O(1); a meet, a join and a difference of sets
// of m <= n pieces split one set around each piece of the other and are O(m log(n/m + 1)):
// O(log n) for one piece, O(n) for two sets of n as the merge of two lists; an inclusion test
// is O(m log n); a test or search O(log p); the hull, the count and an inequality O(1); the
// longest gap O(1) for each node that does not hold its run yet, so O(log p) after a
// one-piece change to a set already asked. The runs are filled on demand, not as a node is
// built, because a run is a difference of two ends and the ends can be numbers whose
// difference costs time and space in their width (the chains of `l01_25_preimage_catalog`
// s22.rs and the nested squares of powers.rs, which never ask for a gap); for the same
// reason a meet does not add 1 to an end it keeps. An inclusion test and an equality test
// walk both trees together and pass by every subtree the two share, and every subtree of one
// that lies inside a piece of the other, so sets that differ on d paths cost O(d log p) and
// equal sets built apart O(p); a meet or join that leaves an operand unchanged returns its
// tree shared, so the test after it is O(1). Tradeoffs: each piece costs a node of about 150
// bytes, not 32; a meet or join first runs the two inclusion tests that find the shared case;
// a walk over every piece costs a stack of O(log p) nodes; building from a list is O(p) after
// the sort, as before. Test:
// `l01_24_refinement_lattices::scaling::interval_set_operations_scale`; COMPLEXITY.md row
// INTERVAL-persistent.
#[derive(Clone, Default)]
pub struct IntervalSet {
    root: Link,
}

/// A subtree of an [`IntervalSet`]: `None` is the empty one.
type Link = Option<Arc<Node>>;

/// A piece with its hash.
type Keyed = ((End, End), u64);

/// A node of an [`IntervalSet`]'s tree, with the totals of its subtree.
struct Node {
    piece: (End, End),
    piece_hash: u64,
    left: Link,
    right: Link,
    /// The height of the subtree, 1 for a leaf.
    height: u8,
    /// The count of pieces in the subtree.
    count: usize,
    /// The lower end of the subtree's first piece.
    first: End,
    /// The upper end of the subtree's last piece.
    last: End,
    /// The longest run of integers missing between two neighboring pieces of the subtree, 0
    /// for one piece: set by the first [`gap`] that asks for it.
    gap: OnceLock<Num>,
    /// The hash of the subtree's pieces in order: `Σ h_i · R^(count - 1 - i)` modulo `P`.
    hash: u64,
    /// `R^count` modulo `P`.
    pow: u64,
}

/// The modulus of the content hash, the prime `2^61 - 1`.
const P: u64 = (1 << 61) - 1;
/// The base of the content hash.
const R: u64 = 0x0b4f_7e1d_9a35_c2e7 % P;

/// `a · b` modulo `P`, for `a, b < P`.
fn mul_mod(a: u64, b: u64) -> u64 {
    let x = u128::from(a) * u128::from(b);
    let s = (x as u64 & P) + (x >> 61) as u64;
    let s = (s & P) + (s >> 61);
    if s >= P { s - P } else { s }
}

/// `a + b` modulo `P`, for `a, b < P`.
fn add_mod(a: u64, b: u64) -> u64 {
    let s = a + b;
    if s >= P { s - P } else { s }
}

/// A hasher with fixed keys, so that a set's content hash is the same in every run.
struct FixedHasher(u64);

impl std::hash::Hasher for FixedHasher {
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.write_u64(u64::from(b));
        }
    }
    fn write_u64(&mut self, v: u64) {
        self.0 = (self.0 ^ v)
            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
            .rotate_left(29);
    }
    fn write_i64(&mut self, v: i64) {
        self.write_u64(v as u64);
    }
    fn finish(&self) -> u64 {
        let x = self.0 ^ (self.0 >> 31);
        x.wrapping_mul(0xbf58_476d_1ce4_e5b9) ^ (x >> 29)
    }
}

/// The hash of one piece, below `P`.
fn piece_hash(piece: &(End, End)) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = FixedHasher(0x2545_f491_4f6c_dd1d);
    piece.hash(&mut h);
    h.finish() % P
}

/// The integers missing between the upper end `a` of one piece and the lower end `b` of the
/// next: both are finite, since only the outer ends are infinite.
fn run_between(a: &End, b: &End) -> Num {
    match (a, b) {
        (Fin(a), Fin(b)) => &(b - a) - &Num::ONE,
        _ => unreachable!("only the outer ends of a set are infinite"),
    }
}

fn height(t: &Link) -> u8 {
    t.as_ref().map_or(0, |n| n.height)
}

/// The node with the given children and piece, which lies between them with at least one
/// integer missing on each side.
fn node(left: Link, (piece, piece_hash): Keyed, right: Link) -> Arc<Node> {
    let (mut hash, mut pow, mut count, mut h) = (0, 1, 1, 0);
    let first = match &left {
        Some(l) => {
            (hash, pow, count, h) = (l.hash, l.pow, count + l.count, l.height);
            l.first.clone()
        }
        None => piece.0.clone(),
    };
    hash = add_mod(mul_mod(hash, R), piece_hash);
    pow = mul_mod(pow, R);
    let last = match &right {
        Some(r) => {
            hash = add_mod(mul_mod(hash, r.pow), r.hash);
            pow = mul_mod(pow, r.pow);
            count += r.count;
            h = h.max(r.height);
            r.last.clone()
        }
        None => piece.1.clone(),
    };
    Arc::new(Node {
        piece,
        piece_hash,
        left,
        right,
        height: h + 1,
        count,
        first,
        last,
        gap: OnceLock::new(),
        hash,
        pow,
    })
}

/// The longest run of integers missing between two neighboring pieces of `n`'s subtree,
/// computed for the nodes that do not hold it yet and kept in them. A node is built without
/// it because a run is a difference of two ends, and the ends can be wide numbers that most
/// sets never need subtracted (the chains of l01_25 s22.rs, whose ends grow by a digit at each
/// step). The nodes a new set shares with an older one keep their runs, so after one
/// [`IntervalSet::max_gap`] of the older set the next costs `O(1)` for each new node.
fn gap(n: &Node) -> &Num {
    n.gap.get_or_init(|| {
        let mut g = Num::ZERO;
        if let Some(l) = &n.left {
            g = run_between(&l.last, &n.piece.0).max(gap(l).clone());
        }
        if let Some(r) = &n.right {
            g = g.max(run_between(&n.piece.1, &r.first)).max(gap(r).clone());
        }
        g
    })
}

/// The children and the piece of `n`, moved out when `n` is not shared and cloned when it is.
fn parts(n: Arc<Node>) -> (Link, Keyed, Link) {
    match Arc::try_unwrap(n) {
        Ok(n) => (n.left, (n.piece, n.piece_hash), n.right),
        Err(n) => (
            n.left.clone(),
            (n.piece.clone(), n.piece_hash),
            n.right.clone(),
        ),
    }
}

fn rotate_left(t: Arc<Node>) -> Arc<Node> {
    let (a, x, r) = parts(t);
    let (b, y, c) = parts(r.expect("a right child to rotate"));
    node(Some(node(a, x, b)), y, c)
}

fn rotate_right(t: Arc<Node>) -> Arc<Node> {
    let (l, y, c) = parts(t);
    let (a, x, b) = parts(l.expect("a left child to rotate"));
    node(a, x, Some(node(b, y, c)))
}

/// The tree of `l`'s pieces, then `k`, then `r`'s, for every piece of `l` below `k` and of `r`
/// above it: `O(|height(l) - height(r)| + 1)`.
fn join(l: Link, k: Keyed, r: Link) -> Arc<Node> {
    let (hl, hr) = (height(&l), height(&r));
    match (l, r) {
        (Some(l), r) if hl > hr + 1 => join_right(l, k, r),
        (l, Some(r)) if hr > hl + 1 => join_left(l, k, r),
        (l, r) => node(l, k, r),
    }
}

fn join_right(tl: Arc<Node>, k: Keyed, tr: Link) -> Arc<Node> {
    let (l, x, c) = parts(tl);
    if height(&c) <= height(&tr) + 1 {
        let t = node(c, k, tr);
        if t.height <= height(&l) + 1 {
            node(l, x, Some(t))
        } else {
            rotate_left(node(l, x, Some(rotate_right(t))))
        }
    } else {
        let t = join_right(c.expect("taller than tr"), k, tr);
        let tall = t.height > height(&l) + 1;
        let t = node(l, x, Some(t));
        if tall { rotate_left(t) } else { t }
    }
}

fn join_left(tl: Link, k: Keyed, tr: Arc<Node>) -> Arc<Node> {
    let (c, x, r) = parts(tr);
    if height(&c) <= height(&tl) + 1 {
        let t = node(tl, k, c);
        if t.height <= height(&r) + 1 {
            node(Some(t), x, r)
        } else {
            rotate_right(node(Some(rotate_left(t)), x, r))
        }
    } else {
        let t = join_left(tl, k, c.expect("taller than tl"));
        let tall = t.height > height(&r) + 1;
        let t = node(Some(t), x, r);
        if tall { rotate_right(t) } else { t }
    }
}

/// The pieces of `t` whose lower end satisfies `goes_left`, and the rest; `goes_left` holds
/// on a prefix of the pieces. `O(log p)`.
fn split(t: Link, goes_left: &impl Fn(&End) -> bool) -> (Link, Link) {
    let Some(n) = t else {
        return (None, None);
    };
    let left = goes_left(&n.piece.0);
    let (l, k, r) = parts(n);
    if left {
        let (rl, rr) = split(r, goes_left);
        (Some(join(l, k, rl)), rr)
    } else {
        let (ll, lr) = split(l, goes_left);
        (ll, Some(join(lr, k, r)))
    }
}

/// The tree without its last piece, and that piece.
fn split_last(t: Arc<Node>) -> (Link, Keyed) {
    let (l, k, r) = parts(t);
    match r {
        None => (l, k),
        Some(r) => {
            let (r, last) = split_last(r);
            (Some(join(l, k, r)), last)
        }
    }
}

/// The tree without its first piece, and that piece.
fn split_first(t: Arc<Node>) -> (Keyed, Link) {
    let (l, k, r) = parts(t);
    match l {
        None => (k, r),
        Some(l) => {
            let (first, l) = split_first(l);
            (first, Some(join(l, k, r)))
        }
    }
}

/// `l`'s pieces then `r`'s, for every piece of `l` below each of `r` with a gap between.
fn concat(l: Link, r: Link) -> Link {
    match (l, r) {
        (l, None) => l,
        (None, r) => r,
        (l, Some(r)) => {
            let (k, r) = split_first(r);
            Some(join(l, k, r))
        }
    }
}

/// A piece with its hash.
fn keyed(piece: (End, End)) -> Keyed {
    let h = piece_hash(&piece);
    (piece, h)
}

/// `t` without its last piece when that piece reaches `lo - 1`, with `lo..=hi` grown to hold
/// it.
fn absorb_last(t: Link, lo: &mut End, hi: &mut End) -> Link {
    match t {
        Some(t) if lo.at_most_succ(&t.last) => {
            let (t, ((l, h), _)) = split_last(t);
            *lo = l;
            if h > *hi {
                *hi = h;
            }
            t
        }
        t => t,
    }
}

/// The union of the pieces of `a` and `b`. `b` is split around the root piece of `a`, that
/// piece takes in every piece of `b` it overlaps or touches, and the unions of the two sides
/// are joined to it after it takes in the pieces of theirs it now touches (Blelloch, Ferizovic
/// and Sun, "Just Join for Parallel Ordered Sets", 2016). `O(m log(n/m + 1))` for `m <= n`
/// pieces: `O(log n)` for one piece and `O(n)` for two sets of `n`, as a merge of two lists.
fn union(a: Link, b: Link) -> Link {
    let (a, b) = match (a, b) {
        (None, t) | (t, None) => return t,
        (Some(a), Some(b)) if Arc::ptr_eq(&a, &b) => return Some(a),
        (Some(a), Some(b)) => (a, b),
    };
    let (la, ((mut lo, mut hi), _), ra) = parts(a);
    let (below, rest) = split(Some(b), &|l| *l < lo);
    let below = absorb_last(below, &mut lo, &mut hi);
    let (merged, above) = split(rest, &|l| l.at_most_succ(&hi));
    if let Some(m) = merged.filter(|m| m.last > hi) {
        hi = m.last.clone();
    }
    // The pieces of the left side from `lo` on lie below the root piece of `a`, so inside
    // `lo..=hi`; the last one before them merges when it reaches `lo - 1`.
    let (left, _) = split(union(la, below), &|l| *l < lo);
    let left = absorb_last(left, &mut lo, &mut hi);
    let (merged, right) = split(union(ra, above), &|l| l.at_most_succ(&hi));
    if let Some(m) = merged.filter(|m| m.last > hi) {
        hi = m.last.clone();
    }
    Some(join(left, keyed((lo, hi)), right))
}

/// The intersection of the pieces of `a` and `b`: `b` is split around the root piece of `a`,
/// its pieces inside that piece are cut to it, and the two sides meet the two sides of `a`.
/// `O(m log(n/m + 1))` for `m <= n` pieces, as [`union`].
fn intersection(a: Link, b: Link) -> Link {
    let (a, b) = match (a, b) {
        (None, _) | (_, None) => return None,
        (Some(a), Some(b)) if Arc::ptr_eq(&a, &b) => return Some(a),
        (Some(a), Some(b)) => (a, b),
    };
    let (la, ((lo, hi), _), ra) = parts(a);
    let (below, rest) = split(Some(b), &|l| *l < lo);
    let (inside, above) = split(rest, &|l| *l <= hi);
    // The last piece below `lo`, when it reaches into `lo..`, and the end past `hi` of the
    // piece that reaches past it: the last inside, or else that one.
    let reach = (below.as_ref())
        .map(|t| t.last.clone())
        .filter(|e| *e >= lo);
    let past = (inside.as_ref().map(|t| &t.last))
        .or(reach.as_ref())
        .filter(|e| **e > hi);
    // The part past `hi` of that piece meets only the pieces of `ra`, which start past
    // `hi + 1`, so it is kept as `lo..=e`: starting it at `hi + 1` would add 1 to `hi`, and
    // adding to a kept power computes an approximation of the power, whose cost grows with
    // its exponent (the nested squares of l01_25 powers.rs).
    let above = match past {
        Some(e) => Some(join(None, keyed((lo.clone(), e.clone())), above)),
        None => above,
    };
    let mut middle = inside.map(|t| {
        if t.last > hi {
            let (t, ((l, _), _)) = split_last(t);
            join(t, keyed((l, hi.clone())), None)
        } else {
            t
        }
    });
    if let Some(e) = reach {
        middle = Some(join(None, keyed((lo, e.min(hi.clone()))), middle));
    }
    let left = intersection(la, below);
    concat(concat(left, middle), intersection(ra, above))
}

/// The members of `a` that are not in `b`: `a` is split around the root piece of `b`, its
/// pieces that start inside that piece go, the pieces that reach into it from below or past
/// it are cut, and the two sides lose the two sides of `b`. `O(m log(n/m + 1))` for `m <= n`
/// pieces, as [`union`]; each piece of `b` cuts at most one piece of `a` in two.
fn difference(a: Link, b: Link) -> Link {
    let (a, b) = match (a, b) {
        (None, _) => return None,
        (a, None) => return a,
        (Some(a), Some(b)) if Arc::ptr_eq(&a, &b) => return None,
        (Some(a), Some(b)) => (a, b),
    };
    let (lb, ((lo, hi), _), rb) = parts(b);
    let (below, rest) = split(Some(a), &|l| *l < lo);
    let (inside, above) = split(rest, &|l| *l <= hi);
    let reach = (below.as_ref()).map(|t| t.last.clone());
    let past = (inside.as_ref().map(|t| &t.last))
        .or(reach.as_ref())
        .filter(|e| **e > hi)
        .cloned();
    let below = match below {
        Some(t) if t.last >= lo => {
            let (t, ((l, _), _)) = split_last(t);
            Some(join(t, keyed((l, lo.pred())), None))
        }
        t => t,
    };
    let above = match past {
        Some(e) => Some(join(None, keyed((hi.succ(), e)), above)),
        None => above,
    };
    concat(difference(below, lb), difference(above, rb))
}

/// The last piece of `t`.
fn last_piece(t: &Link) -> Option<&(End, End)> {
    let mut n = t.as_deref()?;
    while let Some(r) = n.right.as_deref() {
        n = r;
    }
    Some(&n.piece)
}

/// The tree of the given pieces, sorted and normalized, balanced: `O(p)`.
fn build(pieces: &mut impl Iterator<Item = (End, End)>, count: usize) -> Link {
    if count == 0 {
        return None;
    }
    let left = build(pieces, count / 2);
    let piece = pieces.next().expect("count pieces");
    let right = build(pieces, count - count / 2 - 1);
    let h = piece_hash(&piece);
    Some(node(left, (piece, h), right))
}

/// The pieces of an [`IntervalSet`] in increasing order, from either end.
#[derive(Clone)]
pub struct Pieces<'a> {
    /// The nodes still to give from the front: each with its left subtree given.
    front: Vec<&'a Node>,
    /// The nodes still to give from the back: each with its right subtree given.
    back: Vec<&'a Node>,
    /// The count of pieces not yet given.
    left: usize,
}

impl<'a> Pieces<'a> {
    fn push_left_spine(&mut self, mut t: Option<&'a Node>) {
        while let Some(n) = t {
            self.front.push(n);
            t = n.left.as_deref();
        }
    }

    fn push_right_spine(&mut self, mut t: Option<&'a Node>) {
        while let Some(n) = t {
            self.back.push(n);
            t = n.right.as_deref();
        }
    }
}

impl<'a> Iterator for Pieces<'a> {
    type Item = &'a (End, End);

    fn next(&mut self) -> Option<Self::Item> {
        if self.left == 0 {
            return None;
        }
        let n = self.front.pop()?;
        self.push_left_spine(n.right.as_deref());
        self.left -= 1;
        Some(&n.piece)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.left, Some(self.left))
    }

    fn count(self) -> usize {
        self.left
    }

    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl DoubleEndedIterator for Pieces<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.left == 0 {
            return None;
        }
        let n = self.back.pop()?;
        self.push_right_spine(n.left.as_deref());
        self.left -= 1;
        Some(&n.piece)
    }
}

impl ExactSizeIterator for Pieces<'_> {}

impl std::iter::FusedIterator for Pieces<'_> {}

/// What a [`Walk`] gives next: a whole subtree, not yet opened, or one piece.
#[derive(Clone, Copy)]
enum Step<'a> {
    Tree(&'a Node),
    Piece(&'a (End, End)),
}

impl<'a> Step<'a> {
    /// The least and the greatest member.
    fn ends(self) -> (&'a End, &'a End) {
        match self {
            Step::Tree(n) => (&n.first, &n.last),
            Step::Piece((lo, hi)) => (lo, hi),
        }
    }
}

/// The pieces of a tree in increasing order, given as whole subtrees where the reader can
/// pass one by, so that two sets that share subtrees are compared in time that grows with
/// their differences, not their sizes ([`IntervalSet::is_subset`], equality).
struct Walk<'a> {
    /// The steps still to give, the next on top.
    stack: Vec<Step<'a>>,
}

impl<'a> Walk<'a> {
    fn of(t: &'a Link) -> Self {
        Walk {
            stack: t.as_deref().map(Step::Tree).into_iter().collect(),
        }
    }

    fn next(&self) -> Option<Step<'a>> {
        self.stack.last().copied()
    }

    fn pass(&mut self) {
        self.stack.pop();
    }

    /// Replaces the subtree on top by its left subtree, its piece and its right subtree.
    fn open(&mut self) {
        let Some(Step::Tree(n)) = self.stack.pop() else {
            unreachable!("only a subtree opens");
        };
        self.stack.extend(n.right.as_deref().map(Step::Tree));
        self.stack.push(Step::Piece(&n.piece));
        self.stack.extend(n.left.as_deref().map(Step::Tree));
    }
}

/// Whether `a` and `b` are the same subtree.
fn same(a: Step<'_>, b: Step<'_>) -> bool {
    matches!((a, b), (Step::Tree(x), Step::Tree(y)) if std::ptr::eq(x, y))
}

/// The count of pieces in a step.
fn size(s: Step<'_>) -> usize {
    match s {
        Step::Tree(n) => n.count,
        Step::Piece(_) => 1,
    }
}

impl IntervalSet {
    /// The empty set.
    pub fn empty() -> Self {
        IntervalSet { root: None }
    }

    /// Every integer.
    pub fn top() -> Self {
        IntervalSet::range(NegInf, PosInf)
    }

    /// The integers from `lo` to `hi`, both included; empty when `lo > hi`.
    pub fn range(lo: End, hi: End) -> Self {
        IntervalSet::from_pieces(vec![(lo, hi)])
    }

    /// The one integer `v`.
    pub fn single(v: i64) -> Self {
        IntervalSet::range(End::of(v), End::of(v))
    }

    /// The one integer `v`, of any size.
    pub fn point(v: Num) -> Self {
        IntervalSet::range(Fin(v.clone()), Fin(v))
    }

    /// The integers from `lo` to `hi`, both finite and included.
    pub fn of(lo: i64, hi: i64) -> Self {
        IntervalSet::range(End::of(lo), End::of(hi))
    }

    /// The union of the given pieces, in any order, overlapping or not. A piece whose lower
    /// endpoint is above its upper one, or which has an infinite endpoint on the wrong side, is
    /// empty and is dropped.
    pub fn from_pieces(mut pieces: Vec<(End, End)>) -> Self {
        pieces.retain(|(lo, hi)| lo <= hi && *lo != PosInf && *hi != NegInf);
        pieces.sort();
        let mut out: Vec<(End, End)> = Vec::with_capacity(pieces.len());
        for (lo, hi) in pieces {
            push_merged(&mut out, lo, hi);
        }
        IntervalSet::from_normal(out)
    }

    /// The set of the given pieces, which are sorted, disjoint and not adjacent: `O(p)`.
    fn from_normal(pieces: Vec<(End, End)>) -> Self {
        let count = pieces.len();
        IntervalSet {
            root: build(&mut pieces.into_iter(), count),
        }
    }

    /// The pieces, in increasing order.
    pub fn pieces(&self) -> Pieces<'_> {
        let mut it = Pieces {
            front: Vec::new(),
            back: Vec::new(),
            left: self.len(),
        };
        it.push_left_spine(self.root.as_deref());
        it.push_right_spine(self.root.as_deref());
        it
    }

    /// The pieces from the first whose upper end is at or above `v`, in increasing order:
    /// `O(log p)` to start.
    pub fn pieces_from(&self, v: &End) -> Pieces<'_> {
        self.pieces_after(|(_, hi)| hi < v)
    }

    /// The pieces from the first for which `before` is false, in increasing order, for
    /// `before` true on a prefix of the pieces, as for `partition_point`: `O(log p)` to start.
    pub fn pieces_after(&self, before: impl Fn(&(End, End)) -> bool) -> Pieces<'_> {
        let mut it = Pieces {
            front: Vec::new(),
            back: Vec::new(),
            left: self.len(),
        };
        let mut t = self.root.as_deref();
        while let Some(n) = t {
            if !before(&n.piece) {
                it.front.push(n);
                t = n.left.as_deref();
            } else {
                it.left -= n.left.as_ref().map_or(0, |l| l.count) + 1;
                t = n.right.as_deref();
            }
        }
        it.push_right_spine(self.root.as_deref());
        it
    }

    /// The pieces, in increasing order, taken by value.
    pub fn into_pieces(self) -> Vec<(End, End)> {
        self.pieces().cloned().collect()
    }

    /// The count of pieces: `O(1)`.
    pub fn len(&self) -> usize {
        self.root.as_ref().map_or(0, |n| n.count)
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    /// The first piece: `O(log p)`.
    pub fn first(&self) -> Option<&(End, End)> {
        let mut n = self.root.as_deref()?;
        while let Some(l) = n.left.as_deref() {
            n = l;
        }
        Some(&n.piece)
    }

    /// The last piece: `O(log p)`.
    pub fn last(&self) -> Option<&(End, End)> {
        last_piece(&self.root)
    }

    /// The only piece, when there is exactly one.
    pub fn only(&self) -> Option<&(End, End)> {
        self.root
            .as_deref()
            .filter(|n| n.count == 1)
            .map(|n| &n.piece)
    }

    /// The last piece whose lower end is at or below `v`: the piece that holds `v`, or the
    /// nearest one below it. `O(log p)`.
    pub fn piece_at_or_below(&self, v: &End) -> Option<&(End, End)> {
        let (mut t, mut found) = (self.root.as_deref(), None);
        while let Some(n) = t {
            if n.piece.0 <= *v {
                found = Some(&n.piece);
                t = n.right.as_deref();
            } else {
                t = n.left.as_deref();
            }
        }
        found
    }

    /// The first piece whose upper end is at or above `v`: the piece that holds `v`, or the
    /// nearest one above it. `O(log p)`.
    pub fn piece_at_or_above(&self, v: &End) -> Option<&(End, End)> {
        let (mut t, mut found) = (self.root.as_deref(), None);
        while let Some(n) = t {
            if n.piece.1 >= *v {
                found = Some(&n.piece);
                t = n.left.as_deref();
            } else {
                t = n.right.as_deref();
            }
        }
        found
    }

    /// The length of the longest run of integers missing between two neighboring pieces, 0
    /// for fewer than two pieces: `O(1)` for each node that does not hold its run yet: `O(p)`
    /// the first time, `O(log p)` after a one-piece change to a set already asked.
    pub fn max_gap(&self) -> Num {
        self.root.as_ref().map_or(Num::ZERO, |n| gap(n).clone())
    }

    /// The least and the greatest endpoint, or `None` for the empty set: `O(1)`.
    pub fn bounds(&self) -> Option<(&End, &End)> {
        self.root.as_deref().map(|n| (&n.first, &n.last))
    }

    /// The smallest single interval containing the set.
    pub fn hull(&self) -> Self {
        match self.bounds() {
            Some((lo, hi)) => IntervalSet::range(lo.clone(), hi.clone()),
            None => IntervalSet::empty(),
        }
    }

    /// Whether `v` is a member, by binary search of the pieces.
    pub fn contains(&self, v: i64) -> bool {
        self.contains_end(&End::of(v))
    }

    /// Whether the finite end `v` is a member: `O(log p)`.
    pub fn contains_end(&self, v: &End) -> bool {
        self.piece_at_or_below(v).is_some_and(|(_, hi)| v <= hi)
    }

    /// The finite endpoints, each with whether it is a lower one; the infinities are left out.
    /// Widening decreases their number (see [`IntervalSet::widen`]). `O(1)`.
    pub fn finite_endpoints(&self) -> usize {
        match self.bounds() {
            None => 0,
            Some((lo, hi)) => {
                2 * self.len() - usize::from(*lo == NegInf) - usize::from(*hi == PosInf)
            }
        }
    }

    /// Whether `self` and `other` share their tree, which makes them equal: `O(1)`. The tests
    /// use it to check that an operation returned an operand's tree shared.
    #[cfg(test)]
    fn same_tree(&self, other: &Self) -> bool {
        match (&self.root, &other.root) {
            (Some(a), Some(b)) => Arc::ptr_eq(a, b),
            (None, None) => true,
            _ => false,
        }
    }

    /// The two sets, the one of fewer pieces first.
    fn by_size<'a>(&'a self, other: &'a Self) -> (&'a Self, &'a Self) {
        if self.len() <= other.len() {
            (self, other)
        } else {
            (other, self)
        }
    }

    /// The union. A set that holds the other is returned shared. `O(m log(n/m + 1))` for
    /// `m <= n` pieces, by `union`.
    pub fn join(&self, other: &Self) -> Self {
        let (small, big) = self.by_size(other);
        if small.is_subset(big) {
            return big.clone();
        }
        if big.is_subset(small) {
            return small.clone();
        }
        IntervalSet {
            root: union(small.root.clone(), big.root.clone()),
        }
    }

    /// The intersection. A set inside the other is returned shared. `O(m log(n/m + 1))` for
    /// `m <= n` pieces, by `intersection`.
    pub fn meet(&self, other: &Self) -> Self {
        let (small, big) = self.by_size(other);
        if small.is_subset(big) {
            return small.clone();
        }
        if big.is_subset(small) {
            return big.clone();
        }
        IntervalSet {
            root: intersection(small.root.clone(), big.root.clone()),
        }
    }

    /// Whether every member of `self` is a member of `other`, by one walk of both trees in
    /// increasing order that passes by whole subtrees: one the two sets share, one of `self`
    /// inside a piece of `other`, and one of `other` below what is left of `self`. `O(m log n)`
    /// for `m <= n` pieces, and `O(d log p)` for sets of `p` pieces that differ on `d` of the
    /// paths of their shared tree, as a set and the same set narrowed by one fact do.
    pub fn is_subset(&self, other: &Self) -> bool {
        let (mut a, mut b) = (Walk::of(&self.root), Walk::of(&other.root));
        while let Some(x) = a.next() {
            let Some(y) = b.next() else {
                return false;
            };
            let ((xlo, xhi), (ylo, yhi)) = (x.ends(), y.ends());
            if same(x, y) {
                a.pass();
                b.pass();
            } else if yhi < xlo {
                b.pass();
            } else if xhi < ylo {
                // What `other` has passed by ends below `x`, so nothing holds its least member.
                return false;
            } else if matches!(y, Step::Piece(_)) && ylo <= xlo && xhi <= yhi {
                a.pass();
            } else {
                match (x, y) {
                    // `x` is not inside `y`: below `y` nothing of `other` is left, and its next
                    // piece starts at least one integer past `y`.
                    (Step::Piece(_), Step::Piece(_)) => return false,
                    (Step::Piece(_), Step::Tree(_)) => b.open(),
                    (Step::Tree(_), Step::Piece(_)) => a.open(),
                    (Step::Tree(_), Step::Tree(_)) if size(x) >= size(y) => a.open(),
                    (Step::Tree(_), Step::Tree(_)) => b.open(),
                }
            }
        }
        true
    }

    /// The members of `self` that are not members of `other`. `O(m log(n/m + 1))` for `m <= n`
    /// pieces, by `difference`.
    pub fn minus(&self, other: &Self) -> Self {
        IntervalSet {
            root: difference(self.root.clone(), other.root.clone()),
        }
    }

    /// The set with at most `limit` pieces: while it has more, the two neighboring pieces with
    /// the fewest integers between them merge into their hull, the lower pair on a tie
    /// (sec:constraints). This is not a join and need not be monotone; forward revision applies
    /// it to bound an image by its operands' pieces.
    pub fn cap(&self, limit: usize) -> Self {
        use std::cmp::Reverse;
        use std::collections::BinaryHeap;
        let limit = limit.max(1);
        let n = self.len();
        if n <= limit {
            return self.clone();
        }
        // The pieces as a list linked by index, so that a merge is O(1), and the gaps in a
        // heap, smallest first and the lower pair on a tie; a gap whose pieces have changed
        // since it was pushed is skipped when it comes up. A piece's lower end never changes,
        // so the heap holds the index of the right piece, not its end.
        let mut pieces = self.clone().into_pieces();
        let mut next: Vec<usize> = (1..=n).collect();
        let mut alive = vec![true; n];
        let gap = |left: &(End, End), right: &(End, End)| match (&left.1, &right.0) {
            (Fin(hi), Fin(lo)) => lo - hi,
            _ => unreachable!("only the outer endpoints are infinite"),
        };
        let mut heap: BinaryHeap<Reverse<(Num, usize, usize)>> = (0..n - 1)
            .map(|i| Reverse((gap(&pieces[i], &pieces[i + 1]), i, i + 1)))
            .collect();
        let mut count = n;
        while count > limit {
            let Reverse((_, at, right_was)) = heap.pop().expect("a gap for each pair");
            let right = next[at];
            if !alive[at] || right >= n || right != right_was {
                continue;
            }
            pieces[at].1 = std::mem::replace(&mut pieces[right].1, NegInf);
            alive[right] = false;
            next[at] = next[right];
            if next[at] < n {
                let r = next[at];
                heap.push(Reverse((gap(&pieces[at], &pieces[r]), at, r)));
            }
            count -= 1;
        }
        IntervalSet::from_normal(
            pieces
                .into_iter()
                .zip(alive)
                .filter_map(|(p, a)| a.then_some(p))
                .collect(),
        )
    }

    /// The widening `self ∇ next` (step M0.5), for `next` the value that the join would give,
    /// which contains `self`.
    ///
    /// Each finite endpoint of `next` moves outward to the nearest target: an endpoint of
    /// `self`, of either role, or a landmark; with none on that side, to the infinity there.
    /// A lower endpoint moves down and an upper one up, so the result contains `next`, and
    /// pieces that then touch merge. An endpoint of `self` or a landmark stays where it is.
    ///
    /// So the finite endpoints of every element of an ascending chain of widenings lie in
    /// `K`, the first element's endpoints and the landmarks. An element whose endpoints lie in
    /// `K` is a union of some of the `2|K| + 1` parts into which `K` cuts the line (its points
    /// and the gaps between them), so the chain has at most `2|K| + 2` elements. No count of
    /// pieces or of steps enters. The bottom widens to `next` unchanged.
    ///
    /// Complexity tradeoff: an end that grows past the old ends and the landmarks goes to the
    /// next landmark or to infinity, so a loop's bound that no literal names is lost (a
    /// growing buffer length gets `0..`). Why: the lattice has infinite
    /// ascending chains, so a fixpoint without widening need not be reached; with it a head is
    /// evaluated O(|K|) times. Trigger: a loop whose bound is not among the program's integer
    /// literals plus or minus one. Tests:
    /// `m0_05_widening_and_iteration::widening::a_moved_endpoint_goes_to_the_next_landmark_or_infinity`,
    /// `m0_05_widening_and_iteration::widening::interval_widening_chains_stay_on_the_first_ends_and_the_landmarks`.
    /// COMPLEXITY.md row S13. Narrowing ([`IntervalSet::narrow`]) and the symbolic bounds
    /// (`affine`) recover part of what is lost. A complete solution would solve the loop's
    /// recurrence exactly (acceleration), which is possible for affine loops only and
    /// undecidable in general.
    pub fn widen(&self, next: &Self, marks: &Landmarks) -> Self {
        if self.is_empty() || next == self {
            return next.clone();
        }
        let ends = self.finite_ends();
        let out = next
            .pieces()
            .map(|(lo, hi)| {
                let lo = match lo {
                    Fin(v) => below(&ends, marks, v).map_or(NegInf, Fin),
                    e => e.clone(),
                };
                let hi = match hi {
                    Fin(v) => above(&ends, marks, v).map_or(PosInf, Fin),
                    e => e.clone(),
                };
                (lo, hi)
            })
            .collect();
        IntervalSet::from_pieces(out)
    }

    /// The least set holding `self` whose finite ends are landmarks: each end of each piece
    /// moves out to the nearest landmark on its side, or to infinity when there is none. Its
    /// ends lie in a finite set, so there are finitely many results for one set of landmarks.
    pub fn snap(&self, marks: &Landmarks) -> Self {
        let out = self
            .pieces()
            .map(|(lo, hi)| {
                let lo = match lo {
                    Fin(v) => landmark_below(marks, v).map_or(NegInf, Fin),
                    e => e.clone(),
                };
                let hi = match hi {
                    Fin(v) => landmark_above(marks, v).map_or(PosInf, Fin),
                    e => e.clone(),
                };
                (lo, hi)
            })
            .collect();
        IntervalSet::from_pieces(out)
    }

    /// The narrowing `self Δ next` (step M0.5), for `next ⊑ self`, the meet of `self` with
    /// its projection.
    ///
    /// Each finite endpoint of `next` moves outward to the nearest endpoint of `self` or
    /// landmark, and stays where it is when there is none on that side, which is when the
    /// piece of `self` that holds it runs to infinity there. The target is inside that piece
    /// of `self`, so the result lies between `next` and `self`. Its finite endpoints are
    /// endpoints of `self`, landmarks, or a bound that replaced an infinite one of `self`;
    /// the last happens at most once on each side. So the endpoints of every element of a
    /// descending chain of narrowings lie in a finite set, and the chain is finite by the
    /// argument of [`IntervalSet::widen`].
    ///
    /// Complexity tradeoff: a finite end of `next` moves back out to the nearest end of `self`
    /// or landmark on its side, so a tighter bound that a loop shows between landmarks is lost
    /// (`0..=99` narrowed by `5..=50` stays `0..=99`). Why: interval sets have infinite
    /// descending chains (`0..=99`, `0..=98`, …), so taking the meet at each step need not
    /// end; with this rule a chain of narrowings has O(|K|) elements. Trigger: a finite end of
    /// `next` with an end of `self` or a landmark beyond it on its side. Tests:
    /// `m0_05_widening_and_iteration::widening::a_narrowing_keeps_old_ends_and_takes_a_bound_for_an_infinite_one`,
    /// `m0_05_widening_and_iteration::widening::interval_narrowing_chains_stay_on_the_first_ends_and_the_landmarks`.
    /// COMPLEXITY.md row C8 (S13 measures the widening phase). A complete solution
    /// would compute the greatest fixpoint below the widened one, which needs the loop's
    /// recurrence solved exactly (acceleration): possible for affine loops only, undecidable
    /// in general.
    pub fn narrow(&self, next: &Self, marks: &Landmarks) -> Self {
        let ends = self.finite_ends();
        let out = next
            .pieces()
            .map(|(lo, hi)| {
                let lo = match lo {
                    Fin(v) => Fin(below(&ends, marks, v).unwrap_or_else(|| v.clone())),
                    e => e.clone(),
                };
                let hi = match hi {
                    Fin(v) => Fin(above(&ends, marks, v).unwrap_or_else(|| v.clone())),
                    e => e.clone(),
                };
                (lo, hi)
            })
            .collect();
        IntervalSet::from_pieces(out)
    }

    /// The finite endpoints of `self`, of either role, in order (the pieces are disjoint and
    /// sorted).
    fn finite_ends(&self) -> Vec<&Num> {
        self.pieces()
            .flat_map(|(lo, hi)| [lo, hi])
            .filter_map(|e| match e {
                Fin(v) => Some(v),
                _ => None,
            })
            .collect()
    }

    /// The set of `-x` for each member `x`.
    pub fn neg(&self) -> Self {
        IntervalSet::from_normal(self.pieces().rev().map(|(lo, hi)| (-hi, -lo)).collect())
    }

    /// The image of each piece under `f`, joined.
    pub fn lift1(&self, f: impl Fn(&(End, End)) -> Vec<(End, End)>) -> Self {
        IntervalSet::from_pieces(self.pieces().flat_map(f).collect())
    }

    /// The pieces split at zero into negative, zero and positive parts, so that each part has
    /// one sign (step M0.5's sign-conditioned tonicity). The parts are listed, not merged.
    pub fn sign_parts(&self) -> Vec<(End, End)> {
        [
            IntervalSet::range(NegInf, End::of(-1)),
            IntervalSet::single(0),
            IntervalSet::range(End::of(1), PosInf),
        ]
        .iter()
        .flat_map(|part| self.meet(part).into_pieces())
        .collect()
    }
}

impl PartialEq for IntervalSet {
    /// Equality of sets: `O(1)` for a different count or hash of pieces, and otherwise a walk
    /// of both trees that passes by the subtrees they share, `O(d log p)` for `d` paths that
    /// differ.
    fn eq(&self, other: &Self) -> bool {
        let (Some(x), Some(y)) = (&self.root, &other.root) else {
            return self.is_empty() && other.is_empty();
        };
        if x.count != y.count || x.hash != y.hash {
            return false;
        }
        let (mut a, mut b) = (Walk::of(&self.root), Walk::of(&other.root));
        loop {
            match (a.next(), b.next()) {
                (None, None) => return true,
                (Some(x), Some(y)) if same(x, y) => {
                    a.pass();
                    b.pass();
                }
                (Some(Step::Piece(p)), Some(Step::Piece(q))) => {
                    if p != q {
                        return false;
                    }
                    a.pass();
                    b.pass();
                }
                // At least one is a subtree: the larger one opens.
                (Some(x @ Step::Tree(_)), Some(y)) if size(x) >= size(y) => a.open(),
                (Some(_), Some(_)) => b.open(),
                _ => return false,
            }
        }
    }
}

impl Eq for IntervalSet {}

impl std::hash::Hash for IntervalSet {
    /// The count and the content hash of the pieces: `O(1)`.
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let (count, hash) = self.root.as_ref().map_or((0, 0), |n| (n.count, n.hash));
        state.write_usize(count);
        state.write_u64(hash);
    }
}

impl fmt::Debug for IntervalSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IntervalSet")
            .field("pieces", &self.pieces().collect::<Vec<_>>())
            .finish()
    }
}

impl PartialOrd for IntervalSet {
    /// The lattice order, inclusion; two sets neither of which contains the other are
    /// unordered.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self.is_subset(other), other.is_subset(self)) {
            (true, true) => Some(Ordering::Equal),
            (true, false) => Some(Ordering::Less),
            (false, true) => Some(Ordering::Greater),
            (false, false) => None,
        }
    }
}

impl fmt::Display for IntervalSet {
    /// The form of the design's types, without `int`: `[0..=4]`, `[0..]`, `[..=-1, 1..]`,
    /// `[]` for the empty set and `[..]` for every integer.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (i, (lo, hi)) in self.pieces().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            if let Fin(v) = lo {
                write!(f, "{v}")?;
            }
            match hi {
                Fin(v) => write!(f, "..={v}")?,
                _ => write!(f, "..")?,
            }
        }
        write!(f, "]")
    }
}

/// Appends the piece `lo..=hi` to `out`, whose pieces are sorted and end at or before `lo`'s
/// piece starts, merging it into the last piece when the two overlap or touch.
fn push_merged(out: &mut Vec<(End, End)>, lo: End, hi: End) {
    match out.last_mut() {
        // Overlapping or adjacent: no integer lies between, so the pieces are one.
        Some(last) if lo.at_most_succ(&last.1) => {
            if hi > last.1 {
                last.1 = hi;
            }
        }
        _ => out.push((lo, hi)),
    }
}

/// The greatest landmark at or below `v`.
fn landmark_below(marks: &Landmarks, v: &Num) -> Option<Num> {
    marks.ints().range(..=v).next_back().cloned()
}

/// The least landmark at or above `v`: [`landmark_below`] mirrored.
fn landmark_above(marks: &Landmarks, v: &Num) -> Option<Num> {
    marks.ints().range(v..).next().cloned()
}

/// The greatest of `ends` and the landmarks at or below `v`: where a lower end moves. Two
/// searches, so a widening costs time logarithmic in the landmarks, not linear.
fn below(ends: &[&Num], marks: &Landmarks, v: &Num) -> Option<Num> {
    let e = ends[..ends.partition_point(|&t| t <= v)].last().copied();
    let m = landmark_below(marks, v);
    match (e, m) {
        (Some(a), Some(b)) => Some(a.max(&b).clone()),
        (Some(a), None) => Some(a.clone()),
        (None, b) => b,
    }
}

/// The least of `ends` and the landmarks at or above `v`: where an upper end moves.
fn above(ends: &[&Num], marks: &Landmarks, v: &Num) -> Option<Num> {
    let e = ends.get(ends.partition_point(|&t| t < v)).copied();
    let m = landmark_above(marks, v);
    match (e, m) {
        (Some(a), Some(b)) => Some(a.min(&b).clone()),
        (Some(a), None) => Some(a.clone()),
        (None, b) => b,
    }
}

/// The binary digits of a non-negative `n`: the least `b` with `n < 2^b`.
fn digits(n: &Num) -> Num {
    n.bits()
}

/// `2^e - 1` for `e >= 0`: the largest value of `e` binary digits.
fn ones(e: &Num) -> Num {
    &Num::pow2(e) - &Num::ONE
}

/// The finite value of an end known to be finite.
fn fin(e: &End) -> &Num {
    match e {
        Fin(v) => v,
        _ => unreachable!("a bound of a non-negative operand is finite below"),
    }
}

/// Forward transfer of a bit word (step L1.39a, DESIGN.md sec:domains) or an integer machine
/// operation (step L1.39f, DESIGN.md sec:linalg) on the intervals of its int operands, in
/// parameter order with the width last: a set holding `p(args)` for every tuple of members on
/// which `p` is defined. Each operand is first met with its domain, `int[0..]` for every one
/// but the `x` of `shl` and `shr`, the operands read as `w` digits with `int[0..<2 ^ w]` and
/// the `k` of a funnel shift with `int[0..<w]`, for the largest `w`; an operand left empty
/// gives the empty set, and operands that are each one integer give the word's value. Every end
/// is exact at any size.
///
/// `bitAnd` lies in `0..=min(hi_a, hi_b)`, `bitOr` and `bitXor` below the least power of two
/// above the larger upper bound (`bitOr` from the larger lower bound), `bitNot` in
/// `2^w - 1 - x` over the corners, `popCount` in `0..=digits(hi_x)` (from 1 when 0 is not a
/// member), `leadingZeros` in `w - digits(x)` over the corners, `trailingZeros` in `w` when `x`
/// is 0 and in `0..digits(hi_x)` otherwise, and `rotl` and `rotr` below `2^w`, 0 exactly when
/// `x` is. `shl` and `shr` are the product and the floor quotient by `2^k`, monotone in `x` and,
/// on each sign of `x`, in `k`, so each sign part of each piece of `x` maps by its corners; a
/// shift right by at least the digits of `x` gives 0 or -1, so `k` is read up to those digits.
/// `f64Bits` is in `int[0..<2 ^ 64]`. `mulHi` is monotone in each factor and falls as `w`
/// grows, so it lies in `(lo_a * lo_b) div 2^hi_w ..= (hi_a * hi_b) div 2^lo_w`, below
/// `2^hi_w`; `bitReverse` and `byteSwap` lie below `2^w`, 0 exactly when `x` is, as the
/// rotations do; `pdep` lies in `0..=hi_mask`, since its one digits are some of the mask's;
/// `pext` lies in `0..=min(hi_x, 2^digits(hi_mask) - 1)`, since it moves the digits of `x` it
/// keeps to places no higher and in the same order, and keeps at most `popCount(mask)` of them.
/// DESIGN gives no bound for `funnelShl` and `funnelShr`; they take the hull `0 ..< 2^hi_w`, 0
/// exactly when both halves are.
///
/// Complexity tradeoff: every operand but the `x` of `shl` and `shr` is read by its hull, and
/// the result is at most two intervals, so a hole in an operand is not carried through and the
/// digit-wise words are bounded by their operands' digits, not by the digits they share. Why:
/// these words are not monotone, so an exact image of unions of pieces is a search over the
/// pieces' digits, and the hull rule is O(1) per word; `shl` and `shr` are monotone on each
/// sign and keep their `x` pieces at O(pieces). The machine operations of step L1.39f but
/// `mulHi` are bounded by their width or by one operand's upper end, and the funnel shifts by
/// their width alone. Trigger: an operand of more than one piece, or of more than one value
/// for `bitAnd`, `bitOr`, `bitXor` and the machine operations. Tests:
/// `l01_39a_bit_words::transfer` and `l01_39f_int_machine_ops::transfer`. A complete solution
/// would add the known-bits domain of step L1.40a, which carries the digits fixed in every
/// member. COMPLEXITY.md row C25.
pub fn bit_word(p: Prim, args: &[IntervalSet]) -> IntervalSet {
    let nonneg = IntervalSet::range(End::of(0), PosInf);
    if p == Prim::F64Bits {
        return IntervalSet::range(End::of(0), Fin(ones(&Num::from(64))));
    }
    let shift = matches!(p, Prim::Shl | Prim::Shr);
    let mut xs: Vec<IntervalSet> = args
        .iter()
        .enumerate()
        .map(|(i, a)| match shift && i == 0 {
            true => a.clone(),
            false => a.meet(&nonneg),
        })
        .collect();
    if zed_kernel::bits::has_width(p)
        && let Some((_, Fin(wh))) = xs.last().and_then(IntervalSet::bounds)
    {
        let within = IntervalSet::range(End::of(0), Fin(ones(wh)));
        let below_w = IntervalSet::range(End::of(0), Fin(wh - &Num::ONE));
        for &i in zed_kernel::bits::below_two_pow_width(p) {
            xs[i] = xs[i].meet(&within);
        }
        if let Some(i) = zed_kernel::bits::below_width(p) {
            xs[i] = xs[i].meet(&below_w);
        }
    }
    if xs.iter().any(IntervalSet::is_empty) {
        return IntervalSet::empty();
    }
    // Complexity tradeoff: operands that are each one integer are given to the kernel as
    // values, so a kept one is written out (`Value::from`), at the cost of its digits; the
    // answer is exact. Why: the kernel's words take its own integers, which keep a product of
    // prime powers but not a sum, and the digit-wise words need the digits. Trigger: a bit word
    // all of whose operands are single values and one of them a kept value outside `i128`.
    // Test: `l01_39a_bit_words::kept_ends::single_kept_operands_give_the_value`; COMPLEXITY.md
    // S33. A complete solution would compute `shl`, `shr`, `bitNot`, `leadingZeros` and
    // `trailingZeros` of kept single values by the rules below, which are exact on them, and
    // the digit-wise words of a bare power of 2 from its exponent.
    let one = |s: &IntervalSet| match s.bounds() {
        Some((Fin(a), Fin(b))) if a == b => Some(Value::from(a)),
        _ => None,
    };
    if let Some(vs) = xs.iter().map(one).collect::<Option<Vec<Value>>>() {
        match zed_kernel::bits::word(p, &vs) {
            Ok(Value::Int(v)) => return IntervalSet::single(v),
            Ok(Value::Big(v)) => return IntervalSet::point(Num::from(&*v)),
            Err(zed_kernel::KernelError::Type(_)) => return IntervalSet::empty(),
            // A value the system could not build: the rules below.
            _ => {}
        }
    }
    let b = |i: usize| xs[i].bounds().expect("not empty");
    let mask = |h: &End| match h {
        Fin(v) => Fin(ones(&digits(v))),
        e => e.clone(),
    };
    let (x_lo, x_hi) = b(0);
    match p {
        Prim::BitAnd => IntervalSet::range(End::of(0), x_hi.min(b(1).1).clone()),
        Prim::BitOr => IntervalSet::range(x_lo.max(b(1).0).clone(), mask(x_hi.max(b(1).1))),
        Prim::BitXor => IntervalSet::range(End::of(0), mask(x_hi.max(b(1).1))),
        Prim::PopCount => IntervalSet::range(
            End::of(i64::from(fin(x_lo).signum() > 0)),
            match x_hi {
                Fin(v) => Fin(digits(v)),
                e => e.clone(),
            },
        ),
        Prim::BitNot => {
            let (w_lo, w_hi) = b(1);
            let lo = match x_hi {
                Fin(x) => Fin((&ones(fin(w_lo)) - x).max(Num::ZERO)),
                _ => End::of(0),
            };
            let hi = match w_hi {
                Fin(w) => Fin(&ones(w) - fin(x_lo)),
                e => e.clone(),
            };
            IntervalSet::range(lo, hi)
        }
        Prim::LeadingZeros => {
            let (w_lo, w_hi) = b(1);
            let lo = match x_hi {
                Fin(x) => Fin((fin(w_lo) - &digits(x)).max(Num::ZERO)),
                _ => End::of(0),
            };
            let hi = match w_hi {
                Fin(w) => Fin(w - &digits(fin(x_lo))),
                e => e.clone(),
            };
            IntervalSet::range(lo, hi)
        }
        Prim::TrailingZeros => {
            let (w_lo, w_hi) = b(1);
            let mut pieces = Vec::new();
            if fin(x_lo).is_zero() {
                pieces.push((w_lo.clone(), w_hi.clone()));
            }
            let positive = xs[0].meet(&IntervalSet::range(End::of(1), PosInf));
            match positive.bounds() {
                Some((Fin(a), Fin(z))) if a == z => {
                    let t = Fin(a.trailing_zeros());
                    pieces.push((t.clone(), t));
                }
                Some((_, Fin(z))) => {
                    pieces.push((End::of(0), Fin(&digits(z) - &Num::ONE).min(w_hi.clone())))
                }
                Some((_, hi)) => pieces.push((End::of(0), hi.clone().min(w_hi.clone()))),
                None => {}
            }
            IntervalSet::from_pieces(pieces)
        }
        Prim::Rotl | Prim::Rotr => {
            if *x_hi == End::of(0) {
                return IntervalSet::single(0);
            }
            let hi = match b(2).1 {
                Fin(w) => Fin(ones(w)),
                e => e.clone(),
            };
            IntervalSet::range(End::of(i64::from(fin(x_lo).signum() > 0)), hi)
        }
        Prim::MulHi => {
            let (b_lo, b_hi) = b(1);
            let (w_lo, w_hi) = b(2);
            let lo = match w_hi {
                Fin(w) => Fin((fin(x_lo) * fin(b_lo)).div_floor(&Num::pow2(w))),
                _ => End::of(0),
            };
            let hi = match (x_hi, b_hi, w_hi) {
                (Fin(a), Fin(c), Fin(w)) => {
                    Fin((a * c).div_floor(&Num::pow2(fin(w_lo))).min(ones(w)))
                }
                _ => PosInf,
            };
            IntervalSet::range(lo, hi)
        }
        Prim::BitReverse | Prim::ByteSwap => {
            if *x_hi == End::of(0) {
                return IntervalSet::single(0);
            }
            let hi = match b(1).1 {
                Fin(w) => Fin(ones(w)),
                e => e.clone(),
            };
            IntervalSet::range(End::of(i64::from(fin(x_lo).signum() > 0)), hi)
        }
        Prim::Pdep => IntervalSet::range(End::of(0), b(1).1.clone()),
        Prim::Pext => IntervalSet::range(End::of(0), x_hi.clone().min(mask(b(1).1))),
        Prim::FunnelShl | Prim::FunnelShr => {
            if *x_hi == End::of(0) && *b(1).1 == End::of(0) {
                return IntervalSet::single(0);
            }
            let hi = match b(3).1 {
                Fin(w) => Fin(ones(w)),
                e => e.clone(),
            };
            IntervalSet::range(End::of(0), hi)
        }
        Prim::Shl => {
            let (k_lo, k_hi) = b(1);
            let k_lo = Num::pow2(fin(k_lo));
            let k_hi = match k_hi {
                Fin(k) => Some(Num::pow2(k)),
                _ => None,
            };
            xs[0].lift1(|piece| {
                IntervalSet::from_pieces(vec![piece.clone()])
                    .sign_parts()
                    .into_iter()
                    .map(|(lo, hi)| match lo.signum() {
                        0 => (End::of(0), End::of(0)),
                        1 => (
                            Fin(fin(&lo) * &k_lo),
                            match (&hi, &k_hi) {
                                (Fin(h), Some(k)) => Fin(h * k),
                                _ => PosInf,
                            },
                        ),
                        _ => (
                            match (&lo, &k_hi) {
                                (Fin(l), Some(k)) => Fin(l * k),
                                _ => NegInf,
                            },
                            Fin(fin(&hi) * &k_lo),
                        ),
                    })
                    .collect()
            })
        }
        _ => {
            // `shr`: the floor quotient by `2^k`; a shift by at least the digits of `x` gives
            // 0 or -1, as the shift by those digits does, so `k` is read up to them.
            let (k_lo, k_hi) = b(1);
            let shr = |x: &Num, k: Option<&Num>| -> Num {
                let d = digits(x);
                let k = match k {
                    Some(k) if *k < d => k,
                    _ => &d,
                };
                x.div_floor(&Num::pow2(k))
            };
            let k_lo = fin(k_lo);
            let k_hi = match k_hi {
                Fin(k) => Some(k),
                _ => None,
            };
            xs[0].lift1(|piece| {
                IntervalSet::from_pieces(vec![piece.clone()])
                    .sign_parts()
                    .into_iter()
                    .map(|(lo, hi)| match lo.signum() {
                        0 => (End::of(0), End::of(0)),
                        1 => (
                            Fin(shr(fin(&lo), k_hi)),
                            match &hi {
                                Fin(h) => Fin(shr(h, Some(k_lo))),
                                e => e.clone(),
                            },
                        ),
                        _ => (
                            match &lo {
                                Fin(l) => Fin(shr(l, Some(k_lo))),
                                e => e.clone(),
                            },
                            Fin(shr(fin(&hi), k_hi)),
                        ),
                    })
                    .collect()
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn set(pieces: &[(i64, i64)]) -> IntervalSet {
        IntervalSet::from_pieces(
            pieces
                .iter()
                .map(|&(a, b)| (End::of(a), End::of(b)))
                .collect(),
        )
    }

    #[test]
    fn normalization_merges_overlapping_and_adjacent_pieces() {
        assert_eq!(set(&[(5, 7), (0, 2), (3, 3)]), set(&[(0, 3), (5, 7)]));
        assert_eq!(
            set(&[(0, 2), (1, 9)]).into_pieces(),
            [(End::of(0), End::of(9))]
        );
        assert!(set(&[(3, 2)]).is_empty());
        assert_eq!(IntervalSet::range(End::of(i64::MAX), PosInf).len(), 1);
    }

    #[test]
    fn display_uses_the_type_syntax() {
        assert_eq!(set(&[(0, 4)]).to_string(), "[0..=4]");
        assert_eq!(IntervalSet::range(End::of(0), PosInf).to_string(), "[0..]");
        assert_eq!(IntervalSet::top().to_string(), "[..]");
        assert_eq!(
            IntervalSet::from_pieces(vec![(NegInf, End::of(-1)), (End::of(1), PosInf)]).to_string(),
            "[..=-1, 1..]"
        );
        assert_eq!(IntervalSet::empty().to_string(), "[]");
    }

    #[test]
    fn meet_and_join_are_exact_on_small_sets() {
        // Every pair of subsets of 0..6 given as unions: meet and join agree with set algebra.
        let members = |s: &IntervalSet| (0..6).filter(|&v| s.contains(v)).collect::<Vec<_>>();
        let sets: Vec<IntervalSet> = (0u32..64)
            .map(|mask| {
                IntervalSet::from_pieces(
                    (0..6)
                        .filter(|i| mask & (1 << i) != 0)
                        .map(|i| (End::of(i), End::of(i)))
                        .collect(),
                )
            })
            .collect();
        for a in &sets {
            for b in &sets {
                let both: Vec<i64> = members(a).into_iter().filter(|&v| b.contains(v)).collect();
                assert_eq!(members(&a.meet(b)), both);
                let either: Vec<i64> = (0..6).filter(|&v| a.contains(v) || b.contains(v)).collect();
                assert_eq!(members(&a.join(b)), either);
            }
        }
    }

    #[test]
    fn cap_merges_the_smallest_gap_and_the_lower_pair_on_a_tie() {
        let s = set(&[(0, 0), (2, 2), (4, 4), (10, 10)]);
        assert_eq!(s.cap(3), set(&[(0, 2), (4, 4), (10, 10)]));
        assert_eq!(s.cap(2), set(&[(0, 4), (10, 10)]));
        assert_eq!(s.cap(1), set(&[(0, 10)]));
    }

    #[test]
    fn widening_sends_moved_outer_endpoints_to_infinity() {
        let none = Landmarks::none();
        let a = set(&[(0, 2)]);
        assert_eq!(
            a.widen(&set(&[(0, 3)]), &none),
            IntervalSet::range(End::of(0), PosInf)
        );
        assert_eq!(
            a.widen(&set(&[(-1, 2)]), &none),
            IntervalSet::range(NegInf, End::of(2))
        );
        assert_eq!(a.widen(&a, &none), a);
        assert_eq!(IntervalSet::empty().widen(&a, &none), a);
    }

    #[test]
    fn widening_fills_a_gap_that_a_new_inner_endpoint_opens() {
        let none = Landmarks::none();
        // A new piece between two old ones: both of its endpoints are new, so the gaps on both
        // sides are filled.
        let a = set(&[(0, 0), (10, 10)]);
        assert_eq!(
            a.widen(&set(&[(0, 0), (5, 5), (10, 10)]), &none),
            set(&[(0, 10)])
        );
        // An inner endpoint that moves down joins its piece to the one below.
        let a = set(&[(0, 0), (10, 20)]);
        assert_eq!(a.widen(&set(&[(0, 0), (9, 20)]), &none), set(&[(0, 20)]));
    }

    /// A xorshift generator, so that the random tests repeat.
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n: u64) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0 % n
        }

        fn int(&mut self, lo: i64, hi: i64) -> i64 {
            lo + self.below((hi - lo + 1) as u64) as i64
        }
    }

    /// A random set of up to `most` raw pieces with ends in `-w..=w`, overlapping, adjacent or
    /// single points, with an unbounded end on either side now and then.
    fn random_set(rng: &mut Rng, most: u64, w: i64) -> IntervalSet {
        let n = rng.below(most + 1);
        let mut raw = Vec::new();
        for _ in 0..n {
            let lo = rng.int(-w, w);
            let hi = match rng.below(4) {
                0 => lo,
                _ => (lo + rng.int(0, 1 + w / 8)).min(w),
            };
            raw.push((End::of(lo), End::of(hi)));
        }
        if rng.below(5) == 0 {
            raw.push((NegInf, End::of(rng.int(-w, w))));
        }
        if rng.below(5) == 0 {
            raw.push((End::of(rng.int(-w, w)), PosInf));
        }
        IntervalSet::from_pieces(raw)
    }

    /// The members of `s` in `-w-3..=w+3`, beyond which membership no longer changes.
    fn members(s: &IntervalSet, w: i64) -> Vec<bool> {
        (-w - 3..=w + 3).map(|v| s.contains(v)).collect()
    }

    /// The pieces of the set with the given members in `-w-3..=w+3`, found as runs of
    /// members, the outer runs unbounded when they reach the ends: the Vec version.
    fn from_members(m: &[bool], w: i64) -> Vec<(End, End)> {
        let mut out: Vec<(End, End)> = Vec::new();
        let mut start = None;
        for (i, &b) in m.iter().enumerate() {
            let v = -w - 3 + i as i64;
            match (b, start) {
                (true, None) => start = Some(v),
                (false, Some(s)) => {
                    out.push((End::of(s), End::of(v - 1)));
                    start = None;
                }
                _ => {}
            }
        }
        if let Some(s) = start {
            out.push((End::of(s), PosInf));
        }
        if m.first() == Some(&true) {
            out[0].0 = NegInf;
        }
        out
    }

    /// Checks the tree's balance and every summary it keeps against its pieces.
    fn check_tree(t: &Link) -> usize {
        let Some(n) = t else { return 0 };
        let (hl, hr) = (check_tree(&n.left), check_tree(&n.right));
        assert!(hl.abs_diff(hr) <= 1, "unbalanced");
        assert_eq!(usize::from(n.height), hl.max(hr) + 1);
        let whole = IntervalSet { root: t.clone() };
        let pieces: Vec<&(End, End)> = whole.pieces().collect();
        assert_eq!(n.count, pieces.len());
        assert_eq!(n.first, pieces[0].0);
        assert_eq!(n.last, pieces[pieces.len() - 1].1);
        assert_eq!(n.piece_hash, piece_hash(&n.piece));
        let mut gap = Num::ZERO;
        let (mut hash, mut pow) = (0, 1);
        for w in pieces.windows(2) {
            assert!(w[0].0 <= w[0].1);
            assert!(w[0].1.succ() < w[1].0, "pieces that touch are merged");
            gap = gap.max(run_between(&w[0].1, &w[1].0));
        }
        for p in &pieces {
            hash = add_mod(mul_mod(hash, R), piece_hash(p));
            pow = mul_mod(pow, R);
        }
        assert_eq!(*super::gap(n), gap);
        assert_eq!((n.hash, n.pow), (hash, pow));
        hl.max(hr) + 1
    }

    /// `s` against the Vec version of the pieces with the members `m`, by every query.
    fn agrees(s: &IntervalSet, m: &[bool], w: i64) {
        check_tree(&s.root);
        let want = from_members(m, w);
        let got: Vec<(End, End)> = s.pieces().cloned().collect();
        assert_eq!(got, want);
        assert_eq!(*s, IntervalSet::from_pieces(want.clone()));
        assert_eq!(s.len(), want.len());
        assert_eq!(s.pieces().count(), want.len());
        assert_eq!(s.pieces().last(), want.last());
        assert_eq!(s.first(), want.first());
        assert_eq!(s.last(), want.last());
        let mut back: Vec<_> = s.pieces().rev().cloned().collect();
        back.reverse();
        assert_eq!(back, want);
        let bounds = want.first().map(|f| (&f.0, &want[want.len() - 1].1));
        assert_eq!(s.bounds(), bounds);
        let gap = want
            .windows(2)
            .map(|p| run_between(&p[0].1, &p[1].0))
            .max()
            .unwrap_or(Num::ZERO);
        assert_eq!(s.max_gap(), gap);
        for v in -w - 3..=w + 3 {
            let e = End::of(v);
            assert_eq!(s.contains(v), m[(v + w + 3) as usize]);
            assert_eq!(
                s.piece_at_or_below(&e),
                want.iter().rev().find(|p| p.0 <= e)
            );
            assert_eq!(s.piece_at_or_above(&e), want.iter().find(|p| p.1 >= e));
            let from: Vec<_> = s.pieces_from(&e).collect();
            let i = want.partition_point(|p| p.1 < e);
            assert_eq!(from, want[i..].iter().collect::<Vec<_>>());
            // From both ends at once: a front and a back that meet.
            let mut it = s.pieces_from(&e);
            let mut both = Vec::new();
            while let Some(p) = it.next() {
                both.push(p);
                if let Some(q) = it.next_back() {
                    both.push(q);
                }
            }
            assert_eq!(both.len(), want.len() - i);
        }
    }

    /// meet, join, minus, complement_in and is_subset on random sets, against the Vec version
    /// built from members: small sets with many shapes, and larger ones with deep trees.
    #[test]
    fn set_operations_agree_with_the_vec_version_on_random_sets() {
        let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
        for (rounds, most, w) in [(4000, 6, 12), (300, 60, 200), (40, 400, 1500)] {
            for _ in 0..rounds {
                let (a, b) = (random_set(&mut rng, most, w), random_set(&mut rng, most, w));
                let (ma, mb) = (members(&a, w), members(&b, w));
                agrees(&a, &ma, w);
                let zip = |f: fn(bool, bool) -> bool| -> Vec<bool> {
                    ma.iter().zip(&mb).map(|(&x, &y)| f(x, y)).collect()
                };
                agrees(&a.meet(&b), &zip(|x, y| x && y), w);
                agrees(&a.join(&b), &zip(|x, y| x || y), w);
                agrees(&a.minus(&b), &zip(|x, y| x && !y), w);
                agrees(&b.minus(&a), &zip(|x, y| y && !x), w);
                agrees(&a.complement_in(&b), &zip(|x, y| y && !x), w);
                let sub = ma.iter().zip(&mb).all(|(&x, &y)| !x || y);
                assert_eq!(a.is_subset(&b), sub, "{a} ⊆ {b}");
                assert_eq!(a == b, ma == mb);
                // A subset made from `b`: the shortcuts return a shared tree.
                let c = b.meet(&a);
                assert!(c.is_subset(&b) && c.is_subset(&a));
                assert_eq!(c.join(&b), b);
                assert!(c.join(&b).same_tree(&b));
                // A set and the same set less one point share all but one path of their tree.
                let k = rng.int(-w - 2, w + 2);
                let point = IntervalSet::single(k);
                let less = a.minus(&point);
                let mut m = ma.clone();
                m[(k + w + 3) as usize] = false;
                agrees(&less, &m, w);
                assert!(less.is_subset(&a));
                assert_eq!(a.is_subset(&less), !a.contains(k));
                assert_eq!(less == a, !a.contains(k));
                let back = less.join(&point.meet(&a));
                assert_eq!(back, a);
                assert!(a.is_subset(&back) && back.is_subset(&a));
                // Two sets of one tree, each less another point, neither inside the other: the
                // operations meet subtrees the two share.
                let j = rng.int(-w - 2, w + 2);
                let other = a.minus(&IntervalSet::single(j));
                let mut n = ma.clone();
                n[(j + w + 3) as usize] = false;
                let pair = |f: fn(bool, bool) -> bool| -> Vec<bool> {
                    m.iter().zip(&n).map(|(&x, &y)| f(x, y)).collect()
                };
                agrees(&less.join(&other), &pair(|x, y| x || y), w);
                agrees(&less.meet(&other), &pair(|x, y| x && y), w);
                agrees(&less.minus(&other), &pair(|x, y| x && !y), w);
                agrees(&other.minus(&less), &pair(|x, y| y && !x), w);
            }
        }
    }

    /// Equal sets built along different paths are equal and hash alike; the hash and the
    /// count alone never decide equality.
    #[test]
    fn equal_sets_built_differently_hash_alike() {
        use std::hash::{DefaultHasher, Hash, Hasher};
        let hash = |s: &IntervalSet| {
            let mut h = DefaultHasher::new();
            s.hash(&mut h);
            h.finish()
        };
        let mut rng = Rng(0x2545_f491_4f6c_dd1d);
        for _ in 0..2000 {
            let (a, b) = (random_set(&mut rng, 12, 40), random_set(&mut rng, 12, 40));
            // (a ∪ b) \ (b \ a) = a, built by splits and joins, not from a's pieces.
            let back = a.join(&b).minus(&b.minus(&a));
            assert_eq!(back, a);
            assert_eq!(hash(&back), hash(&a));
            let union = b.join(&a);
            assert_eq!(union, a.join(&b));
            assert_eq!(hash(&union), hash(&a.join(&b)));
        }
    }

    /// The empty set, every integer, single points and pieces that touch.
    #[test]
    fn edge_sets() {
        let (e, top) = (IntervalSet::empty(), IntervalSet::top());
        assert_eq!(e.meet(&top), e);
        assert_eq!(e.join(&top), top);
        assert_eq!(top.minus(&e), top);
        assert!(top.minus(&top).is_empty());
        assert_eq!(e.max_gap(), Num::ZERO);
        assert_eq!(e.bounds(), None);
        assert_eq!(e.pieces().count(), 0);
        assert_eq!(
            top.minus(&IntervalSet::single(0)),
            IntervalSet::from_pieces(vec![(NegInf, End::of(-1)), (End::of(1), PosInf)])
        );
        // Pieces that touch merge: [0..=2] ∪ [3..=5] is one piece.
        assert_eq!(set(&[(0, 2)]).join(&set(&[(3, 5)])), set(&[(0, 5)]));
        assert_eq!(set(&[(0, 2), (6, 8)]).join(&set(&[(3, 5)])).len(), 1);
        assert_eq!(set(&[(0, 0), (2, 2)]).max_gap(), Num::ONE);
        assert_eq!(set(&[(5, 5)]).minus(&set(&[(5, 5)])), e);
        assert_eq!(
            set(&[(0, 9)]).minus(&set(&[(3, 3)])),
            set(&[(0, 2), (4, 9)])
        );
    }
}
