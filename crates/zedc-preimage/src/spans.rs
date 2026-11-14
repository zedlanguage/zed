//! The spans `[l, h]` of the cases of kept tests on one name ([`crate::product`]'s
//! `KeptTests`), each with the addresses of the tests kept under it, in a persistent tree
//! ordered by `(l, h)`. Each node holds the least `h` of its subtree, so that the spans that
//! lie inside a run of integers the name has no member in, and reach into a part of it just
//! taken out, are found in time that grows with how many there are.
//!
//! Complexity tradeoff: naive, a watched member per span, the least member of the name in the
//! span, moved to the next member when a test takes it out: `O(log k)` a move, but `k` spans
//! that watch one member all move each time it is taken out, so `m` holes cut one after
//! another at that member cost `Θ(k·m)`. An index by `l` alone, or by `h` alone, visits each
//! live span that starts (or ends) inside the run, `Θ(k·m)` again. Used: a treap (Seidel and
//! Aragon, "Randomized search trees", Algorithmica 16, 1996) ordered by `(l, h)` with a
//! priority from a fixed hash of `(l, h)`, each node holding the least `h` below it, as
//! McCreight's priority search tree answers a three-sided query ("Priority search trees",
//! SIAM J. Comput. 14, 1985): the spans with `l` in a range and `h` below a bound in `O((f +
//! 1) log k)` expected for `f` found, where the tree's depth is `O(log k)` in expectation over
//! the hash. The shape depends on the set alone, so two trees of one set are equal as values.
//! Tradeoff: a fixed hash is not random, so an adversary who knows it can make the tree deep;
//! a McCreight tree would bound the depth for every input, at the cost of rebuilding on
//! deletion. Test `l01_39_reduced_product::xst::s4::scaling::holes_cut_one_at_a_time_scale`.

use std::hash::{DefaultHasher, Hash, Hasher};
use std::sync::Arc;

use zedc_lattice::interval::Num;

use crate::address::Address;

type Link = Option<Arc<Node>>;

#[derive(Debug, PartialEq, Eq)]
struct Node {
    l: Num,
    h: Num,
    at: imbl::OrdSet<Address>,
    priority: u64,
    /// The least `h` of this node's subtree.
    least_h: Num,
    left: Link,
    right: Link,
}

/// A persistent set of spans, each with the tests kept under it.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Spans {
    root: Link,
}

/// The priority of the span `[l, h]`: a hash fixed for every run, so that the tree's shape
/// depends on its spans alone.
fn priority(l: &Num, h: &Num) -> u64 {
    let mut s = DefaultHasher::new();
    (l, h).hash(&mut s);
    s.finish()
}

/// Whether `a` goes above `b` in the heap of priorities: the higher priority, ties by key.
fn above(a: &Node, b: &Node) -> bool {
    (a.priority, &a.l, &a.h) > (b.priority, &b.l, &b.h)
}

fn node(n: &Node, left: Link, right: Link, at: imbl::OrdSet<Address>) -> Arc<Node> {
    let mut least_h = n.h.clone();
    for c in [&left, &right].into_iter().flatten() {
        if c.least_h < least_h {
            least_h = c.least_h.clone();
        }
    }
    Arc::new(Node {
        l: n.l.clone(),
        h: n.h.clone(),
        at,
        priority: n.priority,
        least_h,
        left,
        right,
    })
}

/// The spans of `t` below `(l, h)` and those above it; `(l, h)` is not in `t`.
fn split(t: &Link, l: &Num, h: &Num) -> (Link, Link) {
    let Some(n) = t else {
        return (None, None);
    };
    if (&n.l, &n.h) < (l, h) {
        let (a, b) = split(&n.right, l, h);
        (Some(node(n, n.left.clone(), a, n.at.clone())), b)
    } else {
        let (a, b) = split(&n.left, l, h);
        (a, Some(node(n, b, n.right.clone(), n.at.clone())))
    }
}

/// The spans of `a` and of `b`, each of `a`'s below each of `b`'s.
fn merge(a: &Link, b: &Link) -> Link {
    match (a, b) {
        (None, t) | (t, None) => t.clone(),
        (Some(x), Some(y)) if above(x, y) => {
            Some(node(x, x.left.clone(), merge(&x.right, b), x.at.clone()))
        }
        (Some(_), Some(y)) => Some(node(y, merge(a, &y.left), y.right.clone(), y.at.clone())),
    }
}

fn insert(t: &Link, new: &Node) -> Arc<Node> {
    match t {
        None => node(new, None, None, new.at.clone()),
        Some(n) if (&n.l, &n.h) == (&new.l, &new.h) => node(
            n,
            n.left.clone(),
            n.right.clone(),
            n.at.clone().union(new.at.clone()),
        ),
        // A span already in the tree has the priority of `new`, so it is not below `n`.
        Some(n) if above(new, n) => {
            let (a, b) = split(t, &new.l, &new.h);
            node(new, a, b, new.at.clone())
        }
        Some(n) if (&new.l, &new.h) < (&n.l, &n.h) => {
            node(n, Some(insert(&n.left, new)), n.right.clone(), n.at.clone())
        }
        Some(n) => node(n, n.left.clone(), Some(insert(&n.right, new)), n.at.clone()),
    }
}

/// Whether the subtree of `n` holds the span `[l, h]`.
fn holds(n: &Node, l: &Num, h: &Num) -> bool {
    let mut t = Some(n);
    while let Some(n) = t {
        match (l, h).cmp(&(&n.l, &n.h)) {
            std::cmp::Ordering::Equal => return true,
            std::cmp::Ordering::Less => t = n.left.as_deref(),
            std::cmp::Ordering::Greater => t = n.right.as_deref(),
        }
    }
    false
}

fn remove(t: &Link, l: &Num, h: &Num, k: &Address) -> Link {
    let n = t.as_ref()?;
    Some(match (l, h).cmp(&(&n.l, &n.h)) {
        std::cmp::Ordering::Less => {
            node(n, remove(&n.left, l, h, k), n.right.clone(), n.at.clone())
        }
        std::cmp::Ordering::Greater => {
            node(n, n.left.clone(), remove(&n.right, l, h, k), n.at.clone())
        }
        std::cmp::Ordering::Equal => {
            let at = n.at.without(k);
            if at.is_empty() {
                return merge(&n.left, &n.right);
            }
            node(n, n.left.clone(), n.right.clone(), at)
        }
    })
}

/// Adds to `out` the tests of the spans of `t` with `l` above `after` and at most `upto`, and
/// `h` below `before`; `None` is no bound.
fn within(
    t: &Link,
    after: Option<&Num>,
    upto: Option<&Num>,
    before: Option<&Num>,
    out: &mut std::collections::BTreeSet<Address>,
) {
    let Some(n) = t else {
        return;
    };
    if before.is_some_and(|b| n.least_h >= *b) {
        return;
    }
    let past = after.is_none_or(|a| n.l > *a);
    let short = upto.is_none_or(|u| n.l <= *u);
    if past && short && before.is_none_or(|b| n.h < *b) {
        out.extend(n.at.iter().cloned());
    }
    if past {
        within(&n.left, after, upto, before, out);
    }
    if short {
        within(&n.right, after, upto, before, out);
    }
}

impl Spans {
    pub(crate) fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    /// Adds the test `k` under the span `[l, h]`. `O(log k)` expected.
    pub(crate) fn insert(&mut self, l: &Num, h: &Num, k: &Address) {
        let new = Node {
            l: l.clone(),
            h: h.clone(),
            at: imbl::OrdSet::unit(k.clone()),
            priority: priority(l, h),
            least_h: h.clone(),
            left: None,
            right: None,
        };
        self.root = Some(insert(&self.root, &new));
    }

    /// Takes the test `k` from the span `[l, h]`, and the span when no test is left under it.
    /// `O(log k)` expected.
    pub(crate) fn remove(&mut self, l: &Num, h: &Num, k: &Address) {
        if self.root.as_deref().is_some_and(|n| holds(n, l, h)) {
            self.root = remove(&self.root, l, h, k);
        }
    }

    /// Adds to `out` the tests of the spans whose `l` is above `after` and at most `upto`, and
    /// whose `h` is below `before`; `None` is no bound. `O((f + 1) log k)` expected for `f`
    /// spans found.
    pub(crate) fn within(
        &self,
        after: Option<&Num>,
        upto: Option<&Num>,
        before: Option<&Num>,
        out: &mut std::collections::BTreeSet<Address>,
    ) {
        within(&self.root, after, upto, before, out);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;
    use zed_kernel::Term;
    use zed_kernel::Value;

    fn addr(i: i64) -> Address {
        Address::of(&Term::Lit(Value::Int(i)))
    }

    fn num(i: i64) -> Num {
        Num::from(i)
    }

    /// The tree's shape and its least ends hold, and the heap order of the priorities.
    fn check(t: &Link) -> usize {
        let Some(n) = t else {
            return 0;
        };
        let mut least = n.h.clone();
        for c in [&n.left, &n.right].into_iter().flatten() {
            assert!(!above(c, n));
            least = least.min(c.least_h.clone());
        }
        if let Some(c) = &n.left {
            assert!((&c.l, &c.h) < (&n.l, &n.h));
        }
        if let Some(c) = &n.right {
            assert!((&c.l, &c.h) > (&n.l, &n.h));
        }
        assert_eq!(least, n.least_h);
        assert!(!n.at.is_empty());
        1 + check(&n.left).max(check(&n.right))
    }

    /// Random inserts, removals and queries agree with a list; one set built in two orders is
    /// one tree; the depth stays near `log2` of the size.
    #[test]
    fn spans_agree_with_a_list() {
        let mut seed = 0x9e37_79b9_7f4a_7c15_u64;
        let mut next = |n: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            (seed % n) as i64
        };
        for round in 0..200 {
            let w = if round % 2 == 0 { 8 } else { 400 };
            let mut s = Spans::default();
            let mut list: BTreeSet<(i64, i64, i64)> = BTreeSet::new();
            for _ in 0..(if round % 2 == 0 { 40 } else { 600 }) {
                let l = next(w as u64);
                let h = l + next(6);
                let k = next(5);
                if next(3) == 0 {
                    s.remove(&num(l), &num(h), &addr(k));
                    list.remove(&(l, h, k));
                } else {
                    s.insert(&num(l), &num(h), &addr(k));
                    list.insert((l, h, k));
                }
                let depth = check(&s.root);
                assert!(depth <= 4 * (64 - (list.len() as u64).leading_zeros() as usize) + 4);
                let (a, u, b) = (next(w as u64) - 1, next(w as u64 + 8), next(w as u64 + 8));
                let pick = [Some(a), None];
                let (a, u, b) = (
                    pick[next(2) as usize],
                    [Some(u), None][next(2) as usize],
                    [Some(b), None][next(2) as usize],
                );
                let mut got = BTreeSet::new();
                s.within(
                    a.map(num).as_ref(),
                    u.map(num).as_ref(),
                    b.map(num).as_ref(),
                    &mut got,
                );
                let want: BTreeSet<Address> = list
                    .iter()
                    .filter(|(l, h, _)| {
                        a.is_none_or(|a| *l > a)
                            && u.is_none_or(|u| *l <= u)
                            && b.is_none_or(|b| *h < b)
                    })
                    .map(|&(_, _, k)| addr(k))
                    .collect();
                assert_eq!(got, want);
            }
            let mut again = Spans::default();
            for &(l, h, k) in list.iter().rev() {
                again.insert(&num(l), &num(h), &addr(k));
            }
            assert_eq!(again, s);
        }
    }
}
