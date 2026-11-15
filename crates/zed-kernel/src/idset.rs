//! Persistent sets of small numbers, for the sets of failures that
//! [`Provenance::origins`](crate::provenance::Provenance::origins) finds: each failure of the
//! result is numbered from 0, and a set holds numbers.
//!
//! A set is a tree of fixed shape. A leaf holds the numbers `0 ..< 4096` above its base as 64
//! words of bits, and an inner node of height `h` holds 64 children of height `h - 1`, so a set
//! of numbers below 4096 is one leaf, and one below 2^18 a node over leaves. A change copies the
//! nodes on its path that another set also holds, and changes in place those no other set holds.
//! Two sets that share a node share everything beneath it, so the union, the intersection and
//! the difference of two sets pass over a node both hold without reading it, and read a leaf
//! both hold in different copies a word at a time.
//!
//! Complexity tradeoff (COMPLEXITY.md K25): the persistent ordered map this replaces
//! (`imbl::OrdMap`, nodes of up to 64 entries) costs `O(log n)` comparisons of the members a
//! lookup, a change or a step of a difference, and its nodes are copied at their length, which
//! grows with the set until a node is full, so the work per step grew with the number of
//! failures. Here a lookup or a change costs `O(height)`, a node copy is always 64 words, and a
//! union, intersection or difference costs `O(64 · height)` for each leaf the two sets hold in
//! different copies: a constant per step for up to 4096 failures, one more level for each
//! factor of 64 past that. Tradeoff: a set of one failure takes a whole leaf, 512 bytes, where
//! the map took a node of one entry; and two sets that share no nodes are read leaf by leaf,
//! `O(n / 64)`, where the map's walk of the smaller set cost `O(min log n)`, less when one set
//! is tiny and the other huge and spread over many leaves.

use std::sync::Arc;

/// The words of a leaf, and the children of an inner node.
const WIDTH: usize = 64;
/// The bits of a number that pick its place in a leaf: 64 words of 64 bits.
const LEAF_BITS: u32 = 12;
/// The bits of a number that pick a child of an inner node.
const FAN_BITS: u32 = 6;

#[derive(Clone)]
enum Node {
    /// The numbers of the leaf's range, one bit each, and how many there are.
    Leaf { words: [u64; WIDTH], len: u32 },
    /// The children, each holding the numbers of its part of the range, and how many there are.
    Inner {
        children: [Option<Arc<Node>>; WIDTH],
        len: u32,
    },
}

impl Node {
    fn len(&self) -> u32 {
        match self {
            Node::Leaf { len, .. } | Node::Inner { len, .. } => *len,
        }
    }

    /// The node of height `height` holding `x` alone.
    fn unit(height: u32, x: u32) -> Node {
        match height {
            0 => {
                let mut words = [0; WIDTH];
                words[word(x)] |= bit(x);
                Node::Leaf { words, len: 1 }
            }
            _ => {
                let mut children = [const { None }; WIDTH];
                children[slot(height, x)] = Some(Arc::new(Node::unit(height - 1, x)));
                Node::Inner { children, len: 1 }
            }
        }
    }
}

/// The word of a leaf that holds `x`.
fn word(x: u32) -> usize {
    (x >> 6) as usize % WIDTH
}

/// The bit of `x` in its word.
fn bit(x: u32) -> u64 {
    1 << (x % 64)
}

/// The bits of a number below those that pick a child of a node of height `height` > 0.
fn shift(height: u32) -> u32 {
    LEAF_BITS + FAN_BITS * (height - 1)
}

/// The child of a node of height `height` > 0 that holds `x`.
fn slot(height: u32, x: u32) -> usize {
    (x >> shift(height)) as usize % WIDTH
}

/// Whether a tree of height `height` holds the number `x`'s place: `x < 2^(12 + 6 height)`.
fn fits(height: u32, x: u32) -> bool {
    let bits = LEAF_BITS + FAN_BITS * height;
    bits >= 32 || x >> bits == 0
}

/// A set of numbers. Cloning it is `O(1)`: the clone shares the tree.
#[derive(Clone, Default)]
pub(crate) struct IdSet {
    /// `None` for the empty set.
    root: Option<Arc<Node>>,
    /// The height of the root; 0 for the empty set.
    height: u32,
}

impl IdSet {
    pub(crate) fn new() -> Self {
        IdSet::default()
    }

    /// The set of `x` alone.
    pub(crate) fn unit(x: u32) -> Self {
        let mut s = IdSet::new();
        s.insert(x);
        s
    }

    pub(crate) fn len(&self) -> usize {
        self.root.as_ref().map_or(0, |r| r.len() as usize)
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    /// Whether the two sets are one tree, so equal without reading them.
    pub(crate) fn ptr_eq(&self, other: &IdSet) -> bool {
        self.height == other.height
            && match (&self.root, &other.root) {
                (None, None) => true,
                (Some(a), Some(b)) => Arc::ptr_eq(a, b),
                _ => false,
            }
    }

    pub(crate) fn contains(&self, x: u32) -> bool {
        if !fits(self.height, x) {
            return false;
        }
        let mut node = self.root.as_deref();
        let mut height = self.height;
        while let Some(n) = node {
            match n {
                Node::Leaf { words, .. } => return words[word(x)] & bit(x) != 0,
                Node::Inner { children, .. } => {
                    node = children[slot(height, x)].as_deref();
                    height -= 1;
                }
            }
        }
        false
    }

    /// Adds `x`; whether it was not in the set.
    pub(crate) fn insert(&mut self, x: u32) -> bool {
        if self.contains(x) {
            return false;
        }
        while !fits(self.height, x) {
            self.root = self.lifted(self.height + 1);
            self.height += 1;
        }
        match &mut self.root {
            None => self.root = Some(Arc::new(Node::unit(self.height, x))),
            Some(root) => insert(root, self.height, x),
        }
        true
    }

    /// Removes `x`; whether it was in the set.
    pub(crate) fn remove(&mut self, x: u32) -> bool {
        if !self.contains(x) {
            return false;
        }
        let root = self.root.as_mut().expect("a set holding x");
        if remove(root, self.height, x) {
            *self = IdSet::new();
        } else {
            *self = IdSet::lowered(self.root.take(), self.height);
        }
        true
    }

    /// The set of the tree `root` of height `height`, at the least height that holds it: an
    /// inner root holding numbers only in its first child is replaced by that child. So every
    /// set has the least height its largest number needs, and a set equal to a node of an
    /// operand lifted to a greater height is that operand's own root.
    fn lowered(mut root: Option<Arc<Node>>, mut height: u32) -> IdSet {
        while let Some(Node::Inner { children, len }) = root.as_deref()
            && children[0].as_ref().is_some_and(|c| c.len() == *len)
        {
            root = children[0].clone();
            height -= 1;
        }
        match root {
            None => IdSet::new(),
            root => IdSet { root, height },
        }
    }

    /// The numbers in increasing order.
    pub(crate) fn iter(&self) -> Iter<'_> {
        let mut it = Iter {
            stack: Vec::new(),
            word: 0,
        };
        if let Some(root) = &self.root {
            it.stack.push(Frame {
                node: root,
                height: self.height,
                base: 0,
                next: 0,
            });
        }
        it
    }

    /// The root, lifted to `height` ≥ the set's height by inner nodes whose first child is the
    /// node below.
    fn lifted(&self, height: u32) -> Option<Arc<Node>> {
        let mut root = self.root.clone();
        for _ in self.height..height {
            root = root.map(|r| {
                let len = r.len();
                let mut children = [const { None }; WIDTH];
                children[0] = Some(r);
                Arc::new(Node::Inner { children, len })
            });
        }
        root
    }

    /// The two sets' roots at the height of the taller.
    fn pair(&self, other: &IdSet) -> (Option<Arc<Node>>, Option<Arc<Node>>, u32) {
        let height = self.height.max(other.height);
        (self.lifted(height), other.lifted(height), height)
    }

    /// The numbers in either set. Where the result equals a node of `a` or `b`, it is that node.
    pub(crate) fn union(a: &IdSet, b: &IdSet) -> IdSet {
        if b.is_empty() || a.ptr_eq(b) {
            return a.clone();
        }
        if a.is_empty() {
            return b.clone();
        }
        let (x, y, height) = a.pair(b);
        let root = union(
            x.as_ref().expect("non-empty"),
            y.as_ref().expect("non-empty"),
        );
        IdSet::lowered(Some(root), height)
    }

    /// The numbers in both sets. Where the result equals a node of `a` or `b`, it is that node.
    pub(crate) fn intersection(a: &IdSet, b: &IdSet) -> IdSet {
        if a.ptr_eq(b) {
            return a.clone();
        }
        if a.is_empty() || b.is_empty() {
            return IdSet::new();
        }
        let (x, y, height) = a.pair(b);
        let root = meet(
            x.as_ref().expect("non-empty"),
            y.as_ref().expect("non-empty"),
        );
        IdSet::lowered(root, height)
    }

    /// The numbers in `a` and not in `b`. Where the result equals a node of `a`, it is that
    /// node.
    pub(crate) fn difference(a: &IdSet, b: &IdSet) -> IdSet {
        if a.ptr_eq(b) || a.is_empty() {
            return IdSet::new();
        }
        if b.is_empty() {
            return a.clone();
        }
        let (x, y, height) = a.pair(b);
        let root = minus(x.as_ref().expect("non-empty"), y.as_ref());
        IdSet::lowered(root, height)
    }

    /// The numbers in one set and not the other, in increasing order, each with whether it is
    /// in `to` (added) or in `from` (removed); `None` once there are more than `limit`.
    pub(crate) fn diff(from: &IdSet, to: &IdSet, limit: usize) -> Option<Vec<(u32, bool)>> {
        let mut out = Vec::new();
        if from.ptr_eq(to) {
            return Some(out);
        }
        let (x, y, height) = from.pair(to);
        diff(x.as_ref(), y.as_ref(), height, 0, limit, &mut out).then_some(out)
    }
}

impl FromIterator<u32> for IdSet {
    fn from_iter<I: IntoIterator<Item = u32>>(xs: I) -> Self {
        let mut s = IdSet::new();
        for x in xs {
            s.insert(x);
        }
        s
    }
}

/// Adds `x`, which `node` of height `height` does not hold, copying the nodes on its path that
/// other sets hold.
fn insert(node: &mut Arc<Node>, height: u32, x: u32) {
    match Arc::make_mut(node) {
        Node::Leaf { words, len } => {
            words[word(x)] |= bit(x);
            *len += 1;
        }
        Node::Inner { children, len } => {
            let child = &mut children[slot(height, x)];
            match child {
                Some(c) => insert(c, height - 1, x),
                None => *child = Some(Arc::new(Node::unit(height - 1, x))),
            }
            *len += 1;
        }
    }
}

/// Removes `x`, which `node` of height `height` holds; whether the node is left empty.
fn remove(node: &mut Arc<Node>, height: u32, x: u32) -> bool {
    match Arc::make_mut(node) {
        Node::Leaf { words, len } => {
            words[word(x)] &= !bit(x);
            *len -= 1;
            *len == 0
        }
        Node::Inner { children, len } => {
            let child = &mut children[slot(height, x)];
            if remove(child.as_mut().expect("a child holding x"), height - 1, x) {
                *child = None;
            }
            *len -= 1;
            *len == 0
        }
    }
}

/// The union of two nodes of one height, sharing what it can.
fn union(a: &Arc<Node>, b: &Arc<Node>) -> Arc<Node> {
    if Arc::ptr_eq(a, b) {
        return a.clone();
    }
    match (&**a, &**b) {
        (Node::Leaf { words: x, .. }, Node::Leaf { words: y, .. }) => {
            let mut words = [0; WIDTH];
            let (mut len, mut is_a, mut is_b) = (0, true, true);
            for i in 0..WIDTH {
                let w = x[i] | y[i];
                words[i] = w;
                len += w.count_ones();
                is_a &= w == x[i];
                is_b &= w == y[i];
            }
            match (is_a, is_b) {
                (true, _) => a.clone(),
                (_, true) => b.clone(),
                _ => Arc::new(Node::Leaf { words, len }),
            }
        }
        (Node::Inner { children: x, .. }, Node::Inner { children: y, .. }) => {
            let mut children = [const { None }; WIDTH];
            let (mut len, mut is_a, mut is_b) = (0, true, true);
            for i in 0..WIDTH {
                let c = match (&x[i], &y[i]) {
                    (None, c) | (c, None) => c.clone(),
                    (Some(p), Some(q)) => Some(union(p, q)),
                };
                len += c.as_ref().map_or(0, |c| c.len());
                is_a &= same(&c, &x[i]);
                is_b &= same(&c, &y[i]);
                children[i] = c;
            }
            match (is_a, is_b) {
                (true, _) => a.clone(),
                (_, true) => b.clone(),
                _ => Arc::new(Node::Inner { children, len }),
            }
        }
        _ => unreachable!("nodes of one height"),
    }
}

/// The intersection of two nodes of one height, sharing what it can; `None` when empty.
fn meet(a: &Arc<Node>, b: &Arc<Node>) -> Option<Arc<Node>> {
    if Arc::ptr_eq(a, b) {
        return Some(a.clone());
    }
    match (&**a, &**b) {
        (Node::Leaf { words: x, .. }, Node::Leaf { words: y, .. }) => {
            let mut words = [0; WIDTH];
            let (mut len, mut is_a, mut is_b) = (0, true, true);
            for i in 0..WIDTH {
                let w = x[i] & y[i];
                words[i] = w;
                len += w.count_ones();
                is_a &= w == x[i];
                is_b &= w == y[i];
            }
            match (len, is_a, is_b) {
                (0, ..) => None,
                (_, true, _) => Some(a.clone()),
                (_, _, true) => Some(b.clone()),
                _ => Some(Arc::new(Node::Leaf { words, len })),
            }
        }
        (Node::Inner { children: x, .. }, Node::Inner { children: y, .. }) => {
            let mut children = [const { None }; WIDTH];
            let (mut len, mut is_a, mut is_b) = (0, true, true);
            for i in 0..WIDTH {
                let c = match (&x[i], &y[i]) {
                    (Some(p), Some(q)) => meet(p, q),
                    _ => None,
                };
                len += c.as_ref().map_or(0, |c| c.len());
                is_a &= same(&c, &x[i]);
                is_b &= same(&c, &y[i]);
                children[i] = c;
            }
            match (len, is_a, is_b) {
                (0, ..) => None,
                (_, true, _) => Some(a.clone()),
                (_, _, true) => Some(b.clone()),
                _ => Some(Arc::new(Node::Inner { children, len })),
            }
        }
        _ => unreachable!("nodes of one height"),
    }
}

/// The numbers of `a` not in `b`, nodes of one height, sharing what it can; `None` when empty.
fn minus(a: &Arc<Node>, b: Option<&Arc<Node>>) -> Option<Arc<Node>> {
    let Some(b) = b else {
        return Some(a.clone());
    };
    if Arc::ptr_eq(a, b) {
        return None;
    }
    match (&**a, &**b) {
        (Node::Leaf { words: x, .. }, Node::Leaf { words: y, .. }) => {
            let mut words = [0; WIDTH];
            let (mut len, mut is_a) = (0, true);
            for i in 0..WIDTH {
                let w = x[i] & !y[i];
                words[i] = w;
                len += w.count_ones();
                is_a &= w == x[i];
            }
            match (len, is_a) {
                (0, _) => None,
                (_, true) => Some(a.clone()),
                _ => Some(Arc::new(Node::Leaf { words, len })),
            }
        }
        (Node::Inner { children: x, .. }, Node::Inner { children: y, .. }) => {
            let mut children = [const { None }; WIDTH];
            let (mut len, mut is_a) = (0, true);
            for i in 0..WIDTH {
                let c = x[i].as_ref().and_then(|p| minus(p, y[i].as_ref()));
                len += c.as_ref().map_or(0, |c| c.len());
                is_a &= same(&c, &x[i]);
                children[i] = c;
            }
            match (len, is_a) {
                (0, _) => None,
                (_, true) => Some(a.clone()),
                _ => Some(Arc::new(Node::Inner { children, len })),
            }
        }
        _ => unreachable!("nodes of one height"),
    }
}

/// Whether two children are one node, or both absent.
fn same(a: &Option<Arc<Node>>, b: &Option<Arc<Node>>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(p), Some(q)) => Arc::ptr_eq(p, q),
        _ => false,
    }
}

/// Appends to `out` the numbers in one of `from` and `to`, nodes of height `height` whose range
/// starts at `base`; false once `out` would pass `limit`.
fn diff(
    from: Option<&Arc<Node>>,
    to: Option<&Arc<Node>>,
    height: u32,
    base: u32,
    limit: usize,
    out: &mut Vec<(u32, bool)>,
) -> bool {
    match (from, to) {
        (None, None) => return true,
        (Some(a), Some(b)) if Arc::ptr_eq(a, b) => return true,
        _ => {}
    }
    if height == 0 {
        let words = |n: Option<&Arc<Node>>, i: usize| match n.map(|n| &**n) {
            Some(Node::Leaf { words, .. }) => words[i],
            _ => 0,
        };
        for i in 0..WIDTH {
            let (x, y) = (words(from, i), words(to, i));
            let mut d = x ^ y;
            while d != 0 {
                let b = d.trailing_zeros();
                d &= d - 1;
                if out.len() >= limit {
                    return false;
                }
                out.push((base + ((i as u32) << 6) + b, y >> b & 1 == 1));
            }
        }
        return true;
    }
    fn child(n: Option<&Arc<Node>>, i: usize) -> Option<&Arc<Node>> {
        match n.map(|n| &**n) {
            Some(Node::Inner { children, .. }) => children[i].as_ref(),
            _ => None,
        }
    }
    (0..WIDTH).all(|i| {
        diff(
            child(from, i),
            child(to, i),
            height - 1,
            base + ((i as u32) << shift(height)),
            limit,
            out,
        )
    })
}

/// A node being read by [`Iter`], and the next of its children or words.
struct Frame<'s> {
    node: &'s Node,
    height: u32,
    base: u32,
    next: usize,
}

/// The numbers of a set in increasing order ([`IdSet::iter`]).
pub(crate) struct Iter<'s> {
    stack: Vec<Frame<'s>>,
    /// The bits of the leaf's word last taken not yet given.
    word: u64,
}

impl Iterator for Iter<'_> {
    type Item = u32;

    fn next(&mut self) -> Option<u32> {
        loop {
            let top = self.stack.last_mut()?;
            match top.node {
                Node::Leaf { words, .. } => {
                    if self.word != 0 {
                        let b = self.word.trailing_zeros();
                        self.word &= self.word - 1;
                        return Some(top.base + (((top.next - 1) as u32) << 6) + b);
                    }
                    match top.next {
                        WIDTH => {
                            self.stack.pop();
                        }
                        i => {
                            self.word = words[i];
                            top.next += 1;
                        }
                    }
                }
                Node::Inner { children, .. } => match top.next {
                    WIDTH => {
                        self.stack.pop();
                    }
                    i => {
                        top.next += 1;
                        if let Some(c) = &children[i] {
                            let frame = Frame {
                                node: c,
                                height: top.height - 1,
                                base: top.base + ((i as u32) << shift(top.height)),
                                next: 0,
                            };
                            self.stack.push(frame);
                        }
                    }
                },
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    /// Numbers spread over one leaf, several leaves, and the levels above them.
    fn numbers(seed: u32, n: usize) -> Vec<u32> {
        let mut x = seed;
        (0..n)
            .map(|k| {
                x = x.wrapping_mul(1_103_515_245).wrapping_add(12_345);
                match k % 3 {
                    0 => x % 300,
                    1 => x % 9000,
                    _ => x % 2_000_000,
                }
            })
            .collect()
    }

    fn check(s: &IdSet, t: &BTreeSet<u32>) {
        assert_eq!(s.len(), t.len());
        assert_eq!(s.is_empty(), t.is_empty());
        assert_eq!(
            s.iter().collect::<Vec<_>>(),
            t.iter().copied().collect::<Vec<_>>()
        );
    }

    #[test]
    fn a_set_of_numbers_agrees_with_an_ordered_set() {
        let mut s = IdSet::new();
        let mut t = BTreeSet::new();
        let mut kept = Vec::new();
        for (k, x) in numbers(7, 600).into_iter().enumerate() {
            match k % 4 {
                3 => assert_eq!(s.remove(x), t.remove(&x)),
                _ => assert_eq!(s.insert(x), t.insert(x)),
            }
            assert_eq!(s.contains(x), t.contains(&x));
            if k % 50 == 0 {
                kept.push((s.clone(), t.clone()));
            }
        }
        check(&s, &t);
        // The sets kept along the way are unchanged by the changes made after them.
        for (s, t) in &kept {
            check(s, t);
        }
        for x in t.clone() {
            assert!(s.remove(x));
        }
        assert!(s.is_empty() && s.ptr_eq(&IdSet::new()));
        assert!(!s.contains(5) && !s.contains(u32::MAX));
    }

    #[test]
    fn union_intersection_and_difference_agree_with_ordered_sets() {
        let sets: Vec<(IdSet, BTreeSet<u32>)> = (0..6)
            .map(|seed| {
                let xs = numbers(seed, 40 * seed as usize);
                (xs.iter().copied().collect(), xs.into_iter().collect())
            })
            .collect();
        // Sets made from others, sharing their nodes, and sets of one leaf.
        let mut made = Vec::new();
        for (s, t) in &sets {
            let (mut s, mut t) = (s.clone(), t.clone());
            s.insert(4321);
            t.insert(4321);
            if let Some(&x) = t.iter().next() {
                s.remove(x);
                t.remove(&x);
            }
            made.push((s, t));
        }
        made.push(((0..64).collect(), (0..64).collect()));
        made.push((IdSet::unit(70), BTreeSet::from([70])));
        let all: Vec<&(IdSet, BTreeSet<u32>)> = sets.iter().chain(&made).collect();
        for (a, s) in &all {
            for (b, t) in &all {
                let u = IdSet::union(a, b);
                check(&u, &s.union(t).copied().collect());
                let m = IdSet::intersection(a, b);
                check(&m, &s.intersection(t).copied().collect());
                check(
                    &IdSet::difference(a, b),
                    &s.difference(t).copied().collect(),
                );
                let expected: Vec<(u32, bool)> = s
                    .symmetric_difference(t)
                    .map(|&x| (x, t.contains(&x)))
                    .collect();
                assert_eq!(IdSet::diff(a, b, usize::MAX), Some(expected.clone()));
                let short = IdSet::diff(a, b, expected.len().saturating_sub(1));
                assert_eq!(short.is_none(), !expected.is_empty());
                if m.len() == a.len() {
                    assert!(
                        m.ptr_eq(a) || m.ptr_eq(b),
                        "a meet equal to a set is that set"
                    );
                }
            }
        }
    }
}
