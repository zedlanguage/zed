//! A persistent ordered map: a B-tree whose nodes are shared between maps by reference count,
//! each node allocated at exactly its length. It holds the entries of a
//! [`Family`](crate::value::Family).
//!
//! A node holds at most [`MAX`] entries, and at least [`MIN`] unless it is the root. An inner
//! node of k entries has k + 1 children, with its entries between them, so a key is held once,
//! in the one node where its entry sits, and never copied into the levels above as a B+ tree
//! would copy it. A change copies the nodes on its path from the root that another map also
//! holds, each into a new node of its new length, and changes in place the nodes no other map
//! holds. Two maps that share a node share everything beneath it, so a comparison passes over
//! a node both maps hold without reading it.

use std::cmp::Ordering;
use std::iter::{self, FusedIterator};
use std::mem;
use std::sync::Arc;

/// The most entries a node holds.
const MAX: usize = 16;
/// The fewest entries a node other than the root holds. A node of `MAX + 1` entries splits into
/// two of `MIN` around its middle entry, and two siblings of `MIN - 1` and `MIN` entries merge
/// with the entry between them into one of `MAX`.
const MIN: usize = MAX / 2;

/// A value that stands in the slot of an entry moved out of a node no other map holds, until the
/// node is dropped. Making and dropping it costs nothing: no allocation, no reference count.
pub(crate) trait Hole {
    /// The stand-in.
    fn hole() -> Self;
}

/// An item of a node, moved out of a node no other map holds.
trait Take: Clone {
    /// The item, leaving a stand-in in its place.
    fn take(&mut self) -> Self;
}

impl<K: Hole + Clone, V: Hole + Clone> Take for (K, V) {
    fn take(&mut self) -> Self {
        mem::replace(self, (K::hole(), V::hole()))
    }
}

impl<K: Clone, V: Clone> Take for Branch<K, V> {
    /// The entry is moved; the child's node gets one more holder, given back when the node the
    /// branch came from is dropped. A node has no stand-in that costs nothing: an `Arc` of no
    /// items still allocates its counts.
    fn take(&mut self) -> Self {
        Branch {
            child: self.child.clone(),
            next: self.next.take(),
        }
    }
}

/// Runs `$body` with `$a`, `$m` and `$b`, the items of the node `$node` before `$lo`, from `$lo`
/// to `$hi`, and from `$hi` on, given by value: moved out when no other map holds the node,
/// cloned when one does. The two cases are two iterator types, each of known length, so a node
/// collected from them is allocated once, at its length. The items of `$m` not taken are not
/// cloned.
macro_rules! parts {
    ($node:expr, $lo:expr, $hi:expr, |$a:ident, $m:ident, $b:ident| $body:expr) => {
        match Arc::get_mut($node) {
            Some(items) => {
                let (x, rest) = items.split_at_mut($hi);
                let (x, m) = x.split_at_mut($lo);
                #[allow(unused_mut, reason = "not every body takes from every part")]
                let (mut $a, mut $m, mut $b) = (
                    x.iter_mut().map(Take::take),
                    m.iter_mut().map(Take::take),
                    rest.iter_mut().map(Take::take),
                );
                $body
            }
            None => {
                let (x, rest) = $node.split_at($hi);
                let (x, m) = x.split_at($lo);
                #[allow(unused_mut, reason = "not every body takes from every part")]
                let (mut $a, mut $m, mut $b) =
                    (x.iter().cloned(), m.iter().cloned(), rest.iter().cloned());
                $body
            }
        }
    };
}

/// A map from `K` to `V`, ordered by `K`. A copy costs O(1) and shares every node.
pub(crate) struct Map<K, V> {
    root: Option<Node<K, V>>,
    len: usize,
}

/// A node: its entries in key order, or its branches.
enum Node<K, V> {
    Leaf(Arc<[(K, V)]>),
    /// The k + 1 branches of a node of k entries: each child is followed by the entry after it,
    /// all but the last.
    Inner(Arc<[Branch<K, V>]>),
}

/// A child of an inner node and the entry after it, `None` for the last child.
struct Branch<K, V> {
    child: Node<K, V>,
    next: Option<(K, V)>,
}

impl<K, V> Clone for Node<K, V> {
    fn clone(&self) -> Self {
        match self {
            Node::Leaf(s) => Node::Leaf(Arc::clone(s)),
            Node::Inner(bs) => Node::Inner(Arc::clone(bs)),
        }
    }
}

impl<K: Clone, V: Clone> Clone for Branch<K, V> {
    fn clone(&self) -> Self {
        Branch {
            child: self.child.clone(),
            next: self.next.clone(),
        }
    }
}

/// The entry after the child of `b`, which every branch but an inner node's last holds.
fn entry<K, V>(b: &Branch<K, V>) -> &(K, V) {
    b.next
        .as_ref()
        .expect("every branch but an inner node's last holds an entry")
}

/// Where `k` is among the entries of the inner node `bs`: `Ok(i)` at the entry of branch `i`,
/// `Err(i)` beneath the child of branch `i`.
fn find<K: Ord, V>(bs: &[Branch<K, V>], k: &K) -> Result<usize, usize> {
    bs[..bs.len() - 1].binary_search_by(|b| entry(b).0.cmp(k))
}

impl<K, V> Node<K, V> {
    /// The number of entries in this node, not beneath it.
    fn len(&self) -> usize {
        match self {
            Node::Leaf(s) => s.len(),
            Node::Inner(bs) => bs.len() - 1,
        }
    }

    /// Whether the two are one node, shared.
    fn same(&self, other: &Self) -> bool {
        match (self, other) {
            (Node::Leaf(a), Node::Leaf(b)) => Arc::ptr_eq(a, b),
            (Node::Inner(a), Node::Inner(b)) => Arc::ptr_eq(a, b),
            _ => false,
        }
    }

    /// The number of levels beneath this node: 0 for a leaf.
    fn height(&self) -> usize {
        let mut node = self;
        let mut h = 0;
        while let Node::Inner(bs) = node {
            node = &bs[0].child;
            h += 1;
        }
        h
    }

    /// The least entry beneath this node, which holds at least one.
    fn first(&self) -> &(K, V) {
        let mut node = self;
        loop {
            match node {
                Node::Leaf(s) => return &s[0],
                Node::Inner(bs) => node = &bs[0].child,
            }
        }
    }
}

/// What an insertion beneath a node did.
enum Grown<K, V> {
    /// It replaced an entry.
    Replaced,
    /// It added an entry, and the node kept its place.
    Added,
    /// It added an entry, and the node split: the node holds the lesser half, and the middle
    /// entry and the node of the greater half go to its parent.
    Split((K, V), Node<K, V>),
}

/// Which entry a removal beneath a node takes out.
#[derive(Clone, Copy)]
enum Target<'k, K> {
    /// The entry of this key, which is beneath the node.
    Key(&'k K),
    /// The greatest entry.
    Max,
}

impl<K, V> Default for Map<K, V> {
    fn default() -> Self {
        Map { root: None, len: 0 }
    }
}

impl<K, V> Clone for Map<K, V> {
    fn clone(&self) -> Self {
        Map {
            root: self.root.clone(),
            len: self.len,
        }
    }
}

impl<K, V> Map<K, V> {
    /// The number of entries.
    pub(crate) fn len(&self) -> usize {
        self.len
    }

    /// Whether the map has no entries.
    pub(crate) fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Whether the two maps are one tree, shared, or both empty.
    pub(crate) fn ptr_eq(&self, other: &Self) -> bool {
        match (&self.root, &other.root) {
            (Some(a), Some(b)) => a.same(b),
            (None, None) => true,
            _ => false,
        }
    }

    /// The least entry.
    pub(crate) fn get_min(&self) -> Option<&(K, V)> {
        self.root.as_ref().map(Node::first)
    }

    /// The entries in key order, from either end.
    // Complexity tradeoff: the naive iterator keeps the path from the root as a stack of frames
    // made at its start, O(log n) memory and an allocation even for a map of one node. Used:
    // the frame in hand is kept apart from the stack above it, which is allocated, once and at
    // the tree's height, only when the walk first descends, so a map held in one leaf is walked
    // with no allocation. Each entry costs O(1) amortized, the whole walk O(n), the start
    // O(log n) to find the tree's height. Tradeoff: two cursors, one per end, so the iterator is
    // about twice the size of one.
    pub(crate) fn iter(&self) -> Iter<'_, K, V> {
        let root = self.root.as_ref();
        let height = root.map_or(0, Node::height);
        Iter {
            front: Cursor::new(root, height),
            back: Cursor::new(root, height),
            left: self.len,
        }
    }

    /// The keys in order.
    pub(crate) fn keys(&self) -> impl DoubleEndedIterator<Item = &K> + ExactSizeIterator {
        self.iter().map(|(k, _)| k)
    }

    /// The values in key order.
    pub(crate) fn values(&self) -> impl DoubleEndedIterator<Item = &V> + ExactSizeIterator {
        self.iter().map(|(_, v)| v)
    }

    /// The entries of `self` and `other` side by side in step, the i-th of one with the i-th of
    /// the other ([`Zip::next`]).
    pub(crate) fn zip<'a>(&'a self, other: &'a Self) -> Zip<'a, K, V> {
        Zip {
            a: Cursor::of(self),
            b: Cursor::of(other),
            same: self.ptr_eq(other),
        }
    }

    /// The changes from `self` to `other`, in key order: the entries only `other` holds, those
    /// only `self` holds, and those both hold under one key with values that differ by `!=`.
    // Complexity tradeoff: the naive difference walks both maps in full, O(n + m). Used: two
    // cursors that pass over a subtree both maps hold at once, at any level, without reading
    // it, and descend only into nodes that differ, the taller first, so two maps of which one
    // was made from the other by d changes are compared in O(d log n). Tradeoff: where one
    // cursor faces a node and the other an entry, the node's least key is found, O(log n), to
    // tell whether the entry comes first; this happens only beside a change.
    pub(crate) fn diff<'a, 'b>(&'a self, other: &'b Self) -> Diff<'a, 'b, K, V> {
        // One tree, or two empty ones: no change, and no entry read.
        match self.ptr_eq(other) {
            true => Diff {
                a: Cursor::new(None, 0),
                b: Cursor::new(None, 0),
            },
            false => Diff {
                a: Cursor::of(self),
                b: Cursor::of(other),
            },
        }
    }

    /// The map of the entries `v`, which are in strictly increasing key order.
    // Complexity tradeoff: the naive build inserts the entries one by one, O(n log n), with a
    // copy of each node at each insertion into it and nodes half full after their splits. Used:
    // the tree is laid out at once, O(n): the least height that holds n entries, and at each
    // node as few children as hold its entries, which are spread evenly, so every node is
    // allocated once at its length and holds at least `MIN`. Tradeoff: none in time; a tree
    // built this way is fuller, so an insertion into it splits sooner.
    fn from_sorted(v: Vec<(K, V)>) -> Self {
        let len = v.len();
        if len == 0 {
            return Map::default();
        }
        // `unit` is (MAX + 1)^h: a tree of height h holds at most unit · (MAX + 1) − 1 entries.
        let mut unit = 1usize;
        while unit.checked_mul(MAX + 1).is_some_and(|next| next - 1 < len) {
            unit *= MAX + 1;
        }
        let mut it = v.into_iter();
        let root = build(&mut it, len, unit);
        Map {
            root: Some(root),
            len,
        }
    }
}

/// The node of the next `n` entries of `it`, whose children are of the height h − 1 with
/// `unit` = (MAX + 1)^h; `unit` is 1 for a leaf. A child of height h − 1 holds at most
/// `unit − 1` entries beneath it, so `c = ⌈(n + 1) / unit⌉` children hold the n entries less
/// the c − 1 between them. Since `n + 1 > (c − 1) · unit`, each child gets at least
/// `(n + 1 − c) / c ≥ (c − 1)(unit − 1) / c ≥ (unit − 1) / 2` entries: `MIN` for a leaf, and for
/// an inner child more than `MIN · unit / (MAX + 1)`, so that it in turn has more than `MIN`
/// children. With `n < unit · (MAX + 1)`, `c ≤ MAX + 1`. No node is underfull or overfull.
fn build<K, V, I: Iterator<Item = (K, V)>>(it: &mut I, n: usize, unit: usize) -> Node<K, V> {
    if unit == 1 {
        return Node::Leaf(it.by_ref().take(n).collect());
    }
    let below = unit / (MAX + 1);
    let c = (n + 1).div_ceil(unit);
    let (base, extra) = ((n + 1 - c) / c, (n + 1 - c) % c);
    Node::Inner(
        (0..c)
            .map(|j| Branch {
                child: build(it, base + usize::from(j < extra), below),
                next: (j + 1 < c).then(|| it.next().expect("the entries counted are there")),
            })
            .collect(),
    )
}

impl<K: Ord, V> Map<K, V> {
    /// The value at `k`.
    // Complexity tradeoff: the naive lookup reads the entries in order, O(n). Used: binary
    // search in each node from the root down, O(log n).
    pub(crate) fn get(&self, k: &K) -> Option<&V> {
        let mut node = self.root.as_ref()?;
        loop {
            match node {
                Node::Leaf(s) => return s.binary_search_by(|e| e.0.cmp(k)).ok().map(|i| &s[i].1),
                Node::Inner(bs) => match find(bs, k) {
                    Ok(i) => return Some(&entry(&bs[i]).1),
                    Err(i) => node = &bs[i].child,
                },
            }
        }
    }
}

impl<K: Ord + Clone + Hole, V: Clone + Hole> Map<K, V> {
    /// Puts `v` at `k`, replacing key and value of the entry there if there is one. Returns
    /// whether `k` is new.
    // Complexity tradeoff: the naive persistent map copies itself whole at each change, O(n).
    // Used: path copying, O(log n): the nodes from the root to the entry that another map also
    // holds are copied, each straight to its new length, cloning its items; a node no other
    // map holds is changed in place, or rebuilt at its new length by moving its items out.
    // Tradeoff: a node of k entries is reallocated at each insertion into it, O(MAX) moves, to
    // keep it at exactly its length (no spare room as in imbl's fixed chunks of 16).
    pub(crate) fn insert(&mut self, k: K, v: V) -> bool {
        let Some(root) = &mut self.root else {
            self.root = Some(Node::Leaf(Arc::from([(k, v)])));
            self.len = 1;
            return true;
        };
        match insert_in(root, k, v) {
            Grown::Replaced => return false,
            Grown::Added => {}
            Grown::Split(middle, right) => {
                let left = self.root.take().expect("a split node is the root");
                self.root = Some(Node::Inner(Arc::from([
                    Branch {
                        child: left,
                        next: Some(middle),
                    },
                    Branch {
                        child: right,
                        next: None,
                    },
                ])));
            }
        }
        self.len += 1;
        true
    }

    /// Takes the entry at `k` out. Returns whether there was one.
    // Complexity tradeoff: as for `insert`, path copying, O(log n): the nodes on the path, and
    // the sibling an underfull node borrows from or merges with, are copied if another map holds
    // them, each straight to its new length. Tradeoff: a lookup first, O(log n), so that a key
    // not held copies nothing.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "a family takes no entry out yet; the tests use it"
        )
    )]
    pub(crate) fn remove(&mut self, k: &K) -> bool {
        if self.get(k).is_none() {
            return false;
        }
        self.len -= 1;
        if self.len == 0 {
            self.root = None;
            return true;
        }
        let root = self.root.as_mut().expect("a map holding a key has a root");
        remove_in(root, Target::Key(k));
        // An inner root left with one child gives way to it.
        if let Some(Node::Inner(bs)) = &self.root
            && bs.len() == 1
        {
            self.root = Some(bs[0].child.clone());
        }
        true
    }
}

/// Inserts `(k, v)` beneath `node`.
fn insert_in<K: Ord + Clone + Hole, V: Clone + Hole>(
    node: &mut Node<K, V>,
    k: K,
    v: V,
) -> Grown<K, V> {
    match node {
        Node::Leaf(s) => match s.binary_search_by(|e| e.0.cmp(&k)) {
            Ok(i) => {
                // One length: a copy if another map holds the node, else in place.
                Arc::make_mut(s)[i] = (k, v);
                Grown::Replaced
            }
            Err(i) => {
                let n = s.len() + 1;
                let (left, split) = parts!(s, i, i, |a, _m, b| {
                    let mut all = a.chain(iter::once((k, v))).chain(b);
                    if n <= MAX {
                        (all.collect(), None)
                    } else {
                        let left: Arc<[_]> = all.by_ref().take(MIN).collect();
                        let middle = all.next().expect("a full node has a middle entry");
                        (left, Some((middle, Node::Leaf(all.collect()))))
                    }
                });
                *s = left;
                match split {
                    Some((middle, right)) => Grown::Split(middle, right),
                    None => Grown::Added,
                }
            }
        },
        Node::Inner(bs) => {
            let i = match find(bs, &k) {
                Ok(i) => {
                    Arc::make_mut(bs)[i].next = Some((k, v));
                    return Grown::Replaced;
                }
                Err(i) => i,
            };
            // The child, when another map holds this node: changed apart, then put into one
            // copy of this node at its new length.
            let (child, (middle, right)) = match Arc::get_mut(bs) {
                Some(unique) => match insert_in(&mut unique[i].child, k, v) {
                    Grown::Split(middle, right) => (None, (middle, right)),
                    done => return done,
                },
                None => {
                    let mut child = bs[i].child.clone();
                    match insert_in(&mut child, k, v) {
                        Grown::Split(middle, right) => (Some(child), (middle, right)),
                        done => {
                            *bs = replaced(
                                bs,
                                i,
                                i + 1,
                                [Branch {
                                    child,
                                    next: bs[i].next.clone(),
                                }],
                            );
                            return done;
                        }
                    }
                }
            };
            // Branch i becomes two: its child, now the lesser half, before the middle entry,
            // and the greater half before the entry that followed the child.
            let n = bs.len();
            let (left, split) = parts!(bs, i, i + 1, |a, m, b| {
                let old = m.next().expect("branch i is there");
                let pair = [
                    Branch {
                        child: child.unwrap_or(old.child),
                        next: Some(middle),
                    },
                    Branch {
                        child: right,
                        next: old.next,
                    },
                ];
                let mut all = a.chain(pair).chain(b);
                if n <= MAX {
                    (all.collect(), None)
                } else {
                    let mut middle = None;
                    let left: Arc<[_]> = all
                        .by_ref()
                        .take(MIN + 1)
                        .enumerate()
                        .map(|(j, mut br)| {
                            if j == MIN {
                                middle = br.next.take();
                            }
                            br
                        })
                        .collect();
                    let middle = middle.expect("a full node has a middle entry");
                    (left, Some((middle, Node::Inner(all.collect()))))
                }
            });
            *bs = left;
            match split {
                Some((middle, right)) => Grown::Split(middle, right),
                None => Grown::Added,
            }
        }
    }
}

/// A copy of the inner node `bs` with its branches from `lo` to `hi` replaced by `with`, made
/// at its new length.
fn replaced<K: Clone, V: Clone, const N: usize>(
    bs: &[Branch<K, V>],
    lo: usize,
    hi: usize,
    with: [Branch<K, V>; N],
) -> Arc<[Branch<K, V>]> {
    bs[..lo]
        .iter()
        .cloned()
        .chain(with)
        .chain(bs[hi..].iter().cloned())
        .collect()
}

/// Takes `target` out from beneath `node`, which holds it, and returns the entry under
/// [`Target::Max`]. The node may be left with `MIN − 1` entries, which its parent mends.
fn remove_in<K: Ord + Clone + Hole, V: Clone + Hole>(
    node: &mut Node<K, V>,
    target: Target<'_, K>,
) -> Option<(K, V)> {
    match node {
        Node::Leaf(s) => {
            let i = match target {
                Target::Key(k) => s
                    .binary_search_by(|e| e.0.cmp(k))
                    .expect("the key is beneath the node"),
                Target::Max => s.len() - 1,
            };
            let (rest, out) = parts!(s, i, i + 1, |a, m, b| (
                a.chain(b).collect(),
                // The entry is cloned only when it is wanted.
                matches!(target, Target::Max).then(|| m.next()).flatten()
            ));
            *s = rest;
            out
        }
        Node::Inner(bs) => {
            let (i, here) = match target {
                Target::Key(k) => match find(bs, k) {
                    Ok(i) => (i, true),
                    Err(i) => (i, false),
                },
                Target::Max => (bs.len() - 1, false),
            };
            // An entry here gives way to the greatest entry beneath the child before it.
            let below = if here { Target::Max } else { target };
            match Arc::get_mut(bs) {
                Some(unique) => {
                    let out = remove_in(&mut unique[i].child, below);
                    let out = match here {
                        true => {
                            unique[i].next = out;
                            None
                        }
                        false => out,
                    };
                    if unique[i].child.len() < MIN {
                        let j = sibling(unique, i);
                        let (x, y) = unique.split_at_mut(j + 1);
                        if mend(&mut x[j], &mut y[0]) {
                            *bs = parts!(bs, j + 1, j + 2, |a, _m, b| a.chain(b).collect());
                        }
                    }
                    out
                }
                None => {
                    let mut child = bs[i].child.clone();
                    let out = remove_in(&mut child, below);
                    let (out, next) = match here {
                        true => (None, out),
                        false => (out, bs[i].next.clone()),
                    };
                    let fixed = Branch { child, next };
                    *bs = if fixed.child.len() >= MIN {
                        replaced(bs, i, i + 1, [fixed])
                    } else {
                        let j = sibling(bs, i);
                        let (mut l, mut r) = match j == i {
                            true => (fixed, bs[i + 1].clone()),
                            false => (bs[i - 1].clone(), fixed),
                        };
                        match mend(&mut l, &mut r) {
                            true => replaced(bs, j, j + 2, [l]),
                            false => replaced(bs, j, j + 2, [l, r]),
                        }
                    };
                    out
                }
            }
        }
    }
}

/// The branch `j` such that the underfull child of branch `i` is mended with its sibling,
/// branches `j` and `j + 1`: the one before it if that one can spare an entry or the one after
/// cannot, else the one after.
fn sibling<K, V>(bs: &[Branch<K, V>], i: usize) -> usize {
    match i {
        0 => 0,
        _ if i + 1 < bs.len() && bs[i - 1].child.len() <= MIN && bs[i + 1].child.len() > MIN => i,
        _ => i - 1,
    }
}

/// Mends the two siblings `l.child` and `r.child`, one of them underfull, with `l.next` the entry
/// between them: an entry passes through the parent from the one that can spare it, or the two
/// merge with that entry into `l.child`, which takes `r.next`. Returns whether they merged, when
/// the parent drops `r`. Each sibling is rebuilt at its new length.
fn mend<K: Clone + Hole, V: Clone + Hole>(l: &mut Branch<K, V>, r: &mut Branch<K, V>) -> bool {
    let between = l.next.take().expect("siblings have an entry between them");
    let (ln, rn) = (l.child.len(), r.child.len());
    match (&mut l.child, &mut r.child) {
        (Node::Leaf(x), Node::Leaf(y)) => {
            if ln < MIN && rn > MIN {
                // The least entry of `y` goes up, the entry between goes down to `x`.
                let (rest, up) = parts!(y, 0, 1, |_a, m, b| (b.collect(), m.next()));
                *y = rest;
                *x = parts!(x, ln, ln, |a, _m, _b| a
                    .chain(iter::once(between))
                    .collect());
                l.next = up;
                false
            } else if rn < MIN && ln > MIN {
                let (rest, up) = parts!(x, ln - 1, ln, |a, m, _b| (a.collect(), m.next()));
                *x = rest;
                *y = parts!(y, 0, 0, |_a, _m, b| iter::once(between).chain(b).collect());
                l.next = up;
                false
            } else {
                *x = parts!(x, ln, ln, |a, _m, _b| parts!(y, 0, 0, |_c, _n, d| a
                    .chain(iter::once(between))
                    .chain(d)
                    .collect()));
                l.next = r.next.take();
                true
            }
        }
        (Node::Inner(x), Node::Inner(y)) => {
            if ln < MIN && rn > MIN {
                // The first child of `y` moves to the end of `x`, with the entry between before it.
                let (rest, first) = parts!(y, 0, 1, |_a, m, b| (b.collect(), m.next()));
                *y = rest;
                let first = first.expect("an inner node has a first branch");
                *x = parts!(x, ln, ln + 1, |a, m, _b| {
                    let last = m.next().expect("an inner node has a last branch");
                    a.chain([
                        Branch {
                            child: last.child,
                            next: Some(between),
                        },
                        Branch {
                            child: first.child,
                            next: None,
                        },
                    ])
                    .collect()
                });
                l.next = first.next;
                false
            } else if rn < MIN && ln > MIN {
                // The last child of `x` moves to the front of `y`, the entry before it going up.
                let (rest, up, child) = parts!(x, ln - 1, ln + 1, |a, m, _b| {
                    let before = m
                        .next()
                        .expect("an inner node has a branch before its last");
                    let last = m.next().expect("an inner node has a last branch");
                    let rest = a
                        .chain(iter::once(Branch {
                            child: before.child,
                            next: None,
                        }))
                        .collect();
                    (rest, before.next, last.child)
                });
                *x = rest;
                *y = parts!(y, 0, 0, |_a, _m, b| iter::once(Branch {
                    child,
                    next: Some(between),
                })
                .chain(b)
                .collect());
                l.next = up;
                false
            } else {
                *x = parts!(x, ln, ln + 1, |a, m, _b| {
                    let last = m.next().expect("an inner node has a last branch");
                    parts!(y, 0, 0, |_c, _n, d| a
                        .chain(iter::once(Branch {
                            child: last.child,
                            next: Some(between),
                        }))
                        .chain(d)
                        .collect())
                });
                l.next = r.next.take();
                true
            }
        }
        _ => unreachable!("siblings are of one height"),
    }
}

impl<K: Ord, V> FromIterator<(K, V)> for Map<K, V> {
    /// The map of the entries; of two with one key, the later one.
    // Complexity tradeoff: the naive build inserts the entries one by one, O(n log n) with a
    // node copy at each insertion. Used: a stable sort, O(n) on entries already in order (one
    // run), O(n log n) otherwise, then `from_sorted`, O(n). Tradeoff: a vector of the entries
    // while the tree is built, O(n) memory for that time.
    fn from_iter<I: IntoIterator<Item = (K, V)>>(entries: I) -> Self {
        let mut v: Vec<(K, V)> = entries.into_iter().collect();
        v.sort_by(|x, y| x.0.cmp(&y.0));
        v.dedup_by(|later, kept| {
            let same = later.0 == kept.0;
            if same {
                mem::swap(later, kept);
            }
            same
        });
        Map::from_sorted(v)
    }
}

/// The frame of a cursor in one node: for a leaf, the entries yet to be given; for an inner node,
/// the branches yet to be given, the child of the first (backward: the last) included when the
/// flag is set. An inner frame always holds at least one branch.
enum Frame<'a, K, V> {
    Leaf(&'a [(K, V)]),
    Inner(&'a [Branch<K, V>], bool),
}

impl<K, V> Clone for Frame<'_, K, V> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K, V> Copy for Frame<'_, K, V> {}

/// The frame of the whole of `node`.
fn frame<K, V>(node: &Node<K, V>) -> Frame<'_, K, V> {
    match node {
        Node::Leaf(s) => Frame::Leaf(s),
        Node::Inner(bs) => Frame::Inner(bs, true),
    }
}

/// What a cursor faces.
enum Front<'a, K, V> {
    /// A whole subtree, and its height.
    Node(&'a Node<K, V>, usize),
    Entry(&'a (K, V)),
    End,
}

/// A walk over the entries of a tree in key order, forward, or backward when `BACK` is set,
/// that can pass over a subtree without reading it.
struct Cursor<'a, K, V, const BACK: bool> {
    /// The frame in hand.
    top: Frame<'a, K, V>,
    /// The height of the node of `top`.
    height: usize,
    /// The frames of the nodes above `top`, the root's first.
    above: Vec<Frame<'a, K, V>>,
}

impl<'a, K, V, const BACK: bool> Cursor<'a, K, V, BACK> {
    /// A cursor before the entries of the tree `root`, whose height is `height`.
    fn new(root: Option<&'a Node<K, V>>, height: usize) -> Self {
        Cursor {
            top: root.map_or(Frame::Leaf(&[]), frame),
            height,
            above: Vec::new(),
        }
    }

    /// What the cursor faces, after leaving the frames it has finished.
    fn front(&mut self) -> Front<'a, K, V> {
        loop {
            match self.top {
                Frame::Leaf(s) => {
                    if let Some(e) = if BACK { s.last() } else { s.first() } {
                        return Front::Entry(e);
                    }
                }
                Frame::Inner(bs, true) => {
                    let b = if BACK { &bs[bs.len() - 1] } else { &bs[0] };
                    return Front::Node(&b.child, self.height - 1);
                }
                Frame::Inner(bs, false) => match BACK {
                    false => {
                        if let Some(e) = &bs[0].next {
                            return Front::Entry(e);
                        }
                    }
                    true => {
                        if bs.len() >= 2 {
                            return Front::Entry(entry(&bs[bs.len() - 2]));
                        }
                    }
                },
            }
            match self.above.pop() {
                Some(f) => {
                    self.top = f;
                    self.height += 1;
                }
                None => return Front::End,
            }
        }
    }

    /// Passes over the subtree the cursor faces.
    fn skip(&mut self) {
        if let Frame::Inner(_, child) = &mut self.top {
            *child = false;
        }
    }

    /// Enters the subtree the cursor faces.
    fn descend(&mut self) {
        let Frame::Inner(bs, true) = self.top else {
            unreachable!("a cursor descends only into a subtree it faces");
        };
        let b = if BACK { &bs[bs.len() - 1] } else { &bs[0] };
        if self.above.capacity() == 0 {
            self.above.reserve_exact(self.height);
        }
        self.above.push(Frame::Inner(bs, false));
        self.top = frame(&b.child);
        self.height -= 1;
    }

    /// Passes the entry the cursor faces.
    fn take(&mut self) {
        self.top = match self.top {
            Frame::Leaf(s) => Frame::Leaf(if BACK { &s[..s.len() - 1] } else { &s[1..] }),
            Frame::Inner(bs, _) => {
                Frame::Inner(if BACK { &bs[..bs.len() - 1] } else { &bs[1..] }, true)
            }
        };
    }

    /// The next entry.
    fn next(&mut self) -> Option<&'a (K, V)> {
        loop {
            match self.front() {
                Front::Node(..) => self.descend(),
                Front::Entry(e) => {
                    self.take();
                    return Some(e);
                }
                Front::End => return None,
            }
        }
    }
}

impl<'a, K, V> Cursor<'a, K, V, false> {
    /// A forward cursor before the entries of `m`.
    fn of(m: &'a Map<K, V>) -> Self {
        let root = m.root.as_ref();
        Cursor::new(root, root.map_or(0, Node::height))
    }
}

/// The entries of a map in key order ([`Map::iter`]).
pub(crate) struct Iter<'a, K, V> {
    front: Cursor<'a, K, V, false>,
    back: Cursor<'a, K, V, true>,
    /// The entries neither end has given.
    left: usize,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.left = self.left.checked_sub(1)?;
        self.front.next().map(|(k, v)| (k, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.left, Some(self.left))
    }
}

impl<K, V> DoubleEndedIterator for Iter<'_, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.left = self.left.checked_sub(1)?;
        self.back.next().map(|(k, v)| (k, v))
    }
}

impl<K, V> ExactSizeIterator for Iter<'_, K, V> {}

impl<K, V> FusedIterator for Iter<'_, K, V> {}

/// The next entry of each of two maps, `None` past a map's end ([`Zip::next`]).
pub(crate) type Pair<'a, K, V> = (Option<&'a (K, V)>, Option<&'a (K, V)>);

/// The entries of two maps side by side ([`Map::zip`]).
pub(crate) struct Zip<'a, K, V> {
    a: Cursor<'a, K, V, false>,
    b: Cursor<'a, K, V, false>,
    /// Whether the two maps are one tree, or both empty.
    same: bool,
}

impl<'a, K, V> Zip<'a, K, V> {
    /// The next entry of each map, `None` past a map's end. With `skip`, a run of entries that is
    /// one subtree both maps hold at the same place is passed over, for a comparison under which
    /// every entry equals itself.
    // Complexity tradeoff: the naive walk reads every pair of entries, O(n) for two maps of
    // which one was made from the other by d changes. Used: with `skip`, a subtree both cursors
    // face at once is passed over, and where they face different nodes the taller is entered
    // first, so they meet the shared nodes beneath at the same time: O(d log n) to the end.
    // Tradeoff: none when the maps share nothing; a pair of fronts is matched per step.
    pub(crate) fn next(&mut self, skip: bool) -> Pair<'a, K, V> {
        // The root is passed over as any shared node is, whether or not it is a leaf.
        if skip && self.same {
            return (None, None);
        }
        loop {
            match (self.a.front(), self.b.front()) {
                (Front::Node(x, hx), Front::Node(y, hy)) => {
                    if skip && x.same(y) {
                        self.a.skip();
                        self.b.skip();
                        continue;
                    }
                    if hx >= hy {
                        self.a.descend();
                    }
                    if hy >= hx {
                        self.b.descend();
                    }
                }
                (Front::Node(..), _) => self.a.descend(),
                (_, Front::Node(..)) => self.b.descend(),
                (Front::Entry(e), Front::Entry(f)) => {
                    self.a.take();
                    self.b.take();
                    return (Some(e), Some(f));
                }
                (Front::Entry(e), Front::End) => {
                    self.a.take();
                    return (Some(e), None);
                }
                (Front::End, Front::Entry(f)) => {
                    self.b.take();
                    return (None, Some(f));
                }
                (Front::End, Front::End) => return (None, None),
            }
        }
    }
}

/// A difference between two maps ([`Map::diff`]): the old map's entries have lifetime `'a`, the
/// new map's `'b`.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum DiffItem<'a, 'b, K, V> {
    /// An entry only the new map holds.
    Add(&'b K, &'b V),
    /// A key both hold, with values that differ.
    Update {
        /// The old map's entry.
        old: (&'a K, &'a V),
        /// The new map's entry.
        new: (&'b K, &'b V),
    },
    /// An entry only the old map holds.
    Remove(&'a K, &'a V),
}

/// The changes from one map to another ([`Map::diff`]).
pub(crate) struct Diff<'a, 'b, K, V> {
    a: Cursor<'a, K, V, false>,
    b: Cursor<'b, K, V, false>,
}

impl<'a, 'b, K: Ord, V: PartialEq> Iterator for Diff<'a, 'b, K, V> {
    type Item = DiffItem<'a, 'b, K, V>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match (self.a.front(), self.b.front()) {
                (Front::Node(x, hx), Front::Node(y, hy)) => {
                    if x.same(y) {
                        self.a.skip();
                        self.b.skip();
                        continue;
                    }
                    if hx >= hy {
                        self.a.descend();
                    }
                    if hy >= hx {
                        self.b.descend();
                    }
                }
                (Front::Node(x, _), Front::Entry((k, v))) => {
                    if *k < x.first().0 {
                        self.b.take();
                        return Some(DiffItem::Add(k, v));
                    }
                    self.a.descend();
                }
                (Front::Entry((k, v)), Front::Node(y, _)) => {
                    if *k < y.first().0 {
                        self.a.take();
                        return Some(DiffItem::Remove(k, v));
                    }
                    self.b.descend();
                }
                (Front::Node(..), Front::End) => self.a.descend(),
                (Front::End, Front::Node(..)) => self.b.descend(),
                (Front::Entry((k, v)), Front::Entry((l, w))) => match k.cmp(l) {
                    Ordering::Less => {
                        self.a.take();
                        return Some(DiffItem::Remove(k, v));
                    }
                    Ordering::Greater => {
                        self.b.take();
                        return Some(DiffItem::Add(l, w));
                    }
                    Ordering::Equal => {
                        self.a.take();
                        self.b.take();
                        if v != w {
                            return Some(DiffItem::Update {
                                old: (k, v),
                                new: (l, w),
                            });
                        }
                    }
                },
                (Front::Entry((k, v)), Front::End) => {
                    self.a.take();
                    return Some(DiffItem::Remove(k, v));
                }
                (Front::End, Front::Entry((l, w))) => {
                    self.b.take();
                    return Some(DiffItem::Add(l, w));
                }
                (Front::End, Front::End) => return None,
            }
        }
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod bench;
