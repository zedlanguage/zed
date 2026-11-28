//! Disjoint intervals [lo, hi) of Z_m in a persistent treap ordered by lo, each node carrying
//! an offset still to add to the ends of all below it (a lazy tag, [`treap::lazy`]), so that a
//! whole set of intervals moves by a constant in O(1) (LOAD-max-div-unsolved).

use std::sync::Arc;

use zed_collections::priority::Priorities;
use zed_collections::treap::{self, lazy};
use zedc_int::int::Int;

/// A set of intervals, its root `None` when empty.
#[derive(Clone, Default)]
pub(super) struct Tree(treap::Tree<Span>);

/// An interval [lo, hi) of a node: at a root its own ends; below, its ends less the offsets
/// its ancestors hold ([`Moves`]).
#[derive(Clone)]
struct Span {
    lo: Int,
    hi: Int,
    /// Added to the ends of all below this node.
    off: Int,
}

impl treap::Item for Span {
    type Key = Int;
    type Sum = ();

    fn key(&self) -> &Int {
        &self.lo
    }

    /// [`prio_of`], read once a node, when [`single`] makes it. Not a function of the key, so
    /// these trees are split and joined by [`treap::lazy`] alone, never by `treap::insert` or
    /// `treap::remove`, which rely on one.
    fn priority(&self) -> u64 {
        prio_of()
    }

    fn sum(&self, _: Option<&()>, _: Option<&()>) {}
}

/// The offsets the spans hold, read by the walks of [`treap::lazy`].
struct Moves;

impl lazy::Lazy<Span> for Moves {
    fn pending(&self, s: &Span) -> bool {
        !s.off.is_zero()
    }

    fn under(&self, parent: &Span, child: &Span) -> Span {
        Span {
            lo: &child.lo + &parent.off,
            hi: &child.hi + &parent.off,
            off: &child.off + &parent.off,
        }
    }

    fn clear(&self, s: &mut Span) {
        s.off = Int::ZERO;
    }
}

/// The priorities of the intervals, drawn once per run ([`zed_collections::priority`]).
static PRIORITIES: Priorities = Priorities::new(10);

/// The number of priorities taken so far in the process.
static TAKEN: zed_graph::IdSource = zed_graph::IdSource::starting_at(0);

/// A new interval's priority: the run's random polynomial of degree 4 at the next number of a
/// count kept for the process. A priority fixes only the tree's shape, never the set it holds,
/// so answers do not depend on it. Not drawn from the ends, as in `holes`: a node keeps its
/// ends relative to its offset, and a chain repeating one step makes nodes with the same
/// relative ends at every step, whose equal priorities would make the tree a path (measured:
/// 17 to 33 times the work at n and 8n on such a chain). Nor is it the count itself: the count
/// rises with every interval made, so a tree built in key order would get priorities rising
/// along the keys and be a path of depth n; [`Priorities::of`] hashes the count by the random
/// polynomial, so the order of the counts says nothing about the order of the priorities.
/// Each interval takes its own number,
/// below `P` for any run, so the priorities of the intervals of a tree are 5-wise independent
/// and uniform, and every node's depth is `O(log n)` in expectation (Seidel and Aragon,
/// "Randomized search trees", Algorithmica 16, 1996, doi:10.1007/BF01940876, Theorem 3.3 and
/// section 6; the full comment and the proof are in module [`zed_collections::priority`]), where
/// the fixed sequence this replaces had no bound for chosen intervals (COMPLEXITY.md K123). On
/// one thread the numbers an operation takes depend
/// only on the intervals, never on the shape. Not proved: while other threads take numbers at
/// the same time, which number an interval gets depends on their timing, which the draw can
/// change; the bound assumes it does not (cost only: the number sets the tree's shape, and the
/// intervals the tree holds do not depend on its shape).
fn prio_of() -> u64 {
    PRIORITIES.of(TAKEN.next())
}

/// The set holding [lo, hi) alone.
pub(super) fn single(lo: Int, hi: Int) -> Tree {
    Tree(lazy::single(Span {
        lo,
        hi,
        off: Int::ZERO,
    }))
}

/// `t` moved by d: O(1), making the root again with its ends and offset moved.
pub(super) fn moved(t: &Tree, d: &Int) -> Tree {
    let Some(n) = t.0.as_deref() else {
        return Tree(None);
    };
    if d.is_zero() {
        return t.clone();
    }
    let s = n.item();
    let s = Span {
        lo: &s.lo + d,
        hi: &s.hi + d,
        off: &s.off + d,
    };
    Tree(Some(lazy::mapped(n, s)))
}

/// The intervals of `t` whose lower end is below k, and the others: O(log n) expected,
/// making the path it walks again ([`lazy::split_below`]).
fn split(t: &Tree, k: &Int) -> (Tree, Tree) {
    let (a, b) = lazy::split_below(&t.0, k, &Moves);
    (Tree(a), Tree(b))
}

/// The intervals of `a` and then of `b`, every one of `a` below every one of `b`:
/// O(log n) expected ([`lazy::join`]).
fn join(a: Tree, b: Tree) -> Tree {
    Tree(lazy::join(a.0, b.0, &Moves))
}

/// The first or the last interval of `t`: O(log n) expected.
fn end(t: &Tree, last: bool) -> Option<(Int, Int)> {
    let mut n = t.0.as_deref()?;
    let mut off = Int::ZERO;
    while let Some(c) = (if last { n.right() } else { n.left() }).as_deref() {
        off = &off + &n.item().off;
        n = c;
    }
    let s = n.item();
    Some((&s.lo + &off, &s.hi + &off))
}

/// `t` cut at k: the parts below and above k, an interval holding k cut in two.
pub(super) fn cut(t: &Tree, k: &Int) -> (Tree, Tree) {
    let (a, b) = split(t, k);
    match end(&a, true) {
        Some((lo, hi)) if &hi > k => {
            let a = join(split(&a, &lo).0, single(lo, k.clone()));
            (a, join(single(k.clone(), hi), b))
        }
        _ => (a, b),
    }
}

/// Whether r is in `t`: O(log n) expected.
pub(super) fn holds(t: &Tree, r: &Int) -> bool {
    let mut at = t.0.as_deref();
    let mut off = Int::ZERO;
    let mut hit = false;
    while let Some(n) = at {
        let s = n.item();
        if &s.lo + &off <= *r {
            hit = &s.hi + &off > *r;
            at = n.right().as_deref();
        } else {
            at = n.left().as_deref();
        }
        off = &off + &s.off;
    }
    hit
}

/// Pushes the intervals of `t` on `out` in order, `off` the offsets its ancestors hold: O(n).
fn push_all(t: &treap::Tree<Span>, off: &Int, out: &mut Vec<(Int, Int)>) {
    if let Some(n) = t {
        let s = n.item();
        let below = off + &s.off;
        push_all(n.left(), &below, out);
        out.push((&s.lo + off, &s.hi + off));
        push_all(n.right(), &below, out);
    }
}

/// The union of a set being built, `done` and then the open interval `cur`, with sets every
/// interval of which starts at or after cur's start.
struct Merge {
    done: Tree,
    cur: Option<(Int, Int)>,
}

impl Merge {
    /// The intervals of `t` that start at or before cur's end joined to cur, and the rest.
    fn absorb(&mut self, t: Tree) -> Tree {
        let Some((_, hi)) = self.cur.as_mut() else {
            return t;
        };
        match end(&t, false) {
            Some((lo, _)) if lo <= *hi => {
                let (eaten, rest) = split(&t, &(&*hi + &Int::ONE));
                let (_, top) = end(&eaten, true).expect("eaten holds the first interval");
                if top > *hi {
                    *hi = top;
                }
                rest
            }
            _ => t,
        }
    }

    /// Appends `t`, every interval of which starts at or after cur's start.
    fn append(&mut self, t: Tree) {
        let t = self.absorb(t);
        if let Some((lo, hi)) = end(&t, true) {
            let (body, _) = split(&t, &lo);
            let done = std::mem::take(&mut self.done);
            let cur = self.cur.take().map(|(a, b)| single(a, b));
            self.done = join(join(done, cur.unwrap_or_default()), body);
            self.cur = Some((lo, hi));
        }
    }

    fn finish(self) -> Tree {
        let cur = self.cur.map(|(a, b)| single(a, b));
        join(self.done, cur.unwrap_or_default())
    }
}

/// The union of `a` and `b`, intervals that meet or touch fused.
// Complexity tradeoff: merging the two lists is O(|a| + |b|), which makes a chain of steps
// quadratic. Here each maximal run of one set's intervals in the merged order moves whole
// by a split and a join, and each fused interval costs one split: O((r + f) log n) expected
// for r runs and f fusions. The bound over a chain is at `Shift::apply`.
pub(super) fn union(mut a: Tree, mut b: Tree) -> Tree {
    if a.0.is_none() {
        return b;
    }
    if b.0.is_none() {
        return a;
    }
    let mut out = Merge {
        done: Tree(None),
        cur: None,
    };
    while let (Some((fa, _)), Some((fb, _))) = (end(&a, false), end(&b, false)) {
        if fb < fa {
            std::mem::swap(&mut a, &mut b);
        }
        let first_b = fa.max(fb);
        let (run, rest) = split(&a, &(&first_b + &Int::ONE));
        out.append(run);
        a = rest;
        loop {
            let (na, nb) = (out.absorb(a.clone()), out.absorb(b.clone()));
            let same = ptr_eq(&na, &a) && ptr_eq(&nb, &b);
            (a, b) = (na, nb);
            if same {
                break;
            }
        }
    }
    out.append(a);
    out.append(b);
    out.finish()
}

fn ptr_eq(x: &Tree, y: &Tree) -> bool {
    match (&x.0, &y.0) {
        (None, None) => true,
        (Some(x), Some(y)) => Arc::ptr_eq(x, y),
        _ => false,
    }
}

impl Tree {
    /// The intervals of the set, in order.
    fn listed(&self) -> Vec<(Int, Int)> {
        let mut out = Vec::new();
        push_all(&self.0, &Int::ZERO, &mut out);
        out
    }
}

/// Two sets are equal when they hold the same intervals, whatever their shapes: O(n).
impl PartialEq for Tree {
    fn eq(&self, other: &Tree) -> bool {
        self.listed() == other.listed()
    }
}

impl Eq for Tree {}

impl std::fmt::Debug for Tree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.listed()).finish()
    }
}
