//! Disjoint intervals [lo, hi) of Z_m in a persistent treap ordered by lo, each subtree
//! carrying an offset added to all its ends, so that a whole set of intervals moves by a
//! constant in O(1) (LOAD-max-div-unsolved).

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};

use zed_kernel::priority::Priorities;
use zedc_int::int::Int;

/// A set of intervals, `None` when empty.
pub(super) type Tree = Option<Arc<Node>>;

pub(super) struct Node {
    /// The ends, less the offsets of this node and of its ancestors.
    lo: Int,
    hi: Int,
    /// Added to the ends of this node and of all below it.
    off: Int,
    prio: u64,
    left: Tree,
    right: Tree,
}

/// The priorities of the intervals, drawn once per run ([`zed_kernel::priority`]).
static PRIORITIES: Priorities = Priorities::new(10);

/// The number of priorities taken so far in the process.
static TAKEN: AtomicU64 = AtomicU64::new(0);

/// A new interval's priority: the run's random polynomial of degree 4 at the next number of a
/// count kept for the process. A priority fixes only the tree's shape, never the set it holds,
/// so answers do not depend on it. Not drawn from the ends, as in `holes`: a node keeps its
/// ends relative to its offset, and a chain repeating one step makes nodes with the same
/// relative ends at every step, whose equal priorities would make the tree a path (measured:
/// 17 to 33 times the work at n and 8n on such a chain). Each interval takes its own number,
/// below `P` for any run, so the priorities of the intervals of a tree are 5-wise independent
/// and uniform, and every node's depth is `O(log n)` in expectation (Seidel and Aragon,
/// "Randomized search trees", Algorithmica 16, 1996, Theorem 3.3 and section 6; the proof is in
/// module [`zed_kernel::priority`]), where the fixed sequence this replaces had no bound for
/// chosen intervals (COMPLEXITY.md K123). On one thread the numbers an operation takes depend
/// only on the intervals, never on the shape. Not proved: while other threads take numbers at
/// the same time, which number an interval gets depends on their timing, which the draw can
/// change; the bound assumes it does not.
fn prio_of() -> u64 {
    PRIORITIES.of(TAKEN.fetch_add(1, AtomicOrdering::Relaxed))
}

fn node(lo: Int, hi: Int, off: Int, prio: u64, left: Tree, right: Tree) -> Tree {
    Some(Arc::new(Node {
        lo,
        hi,
        off,
        prio,
        left,
        right,
    }))
}

/// The set holding [lo, hi) alone.
pub(super) fn single(lo: Int, hi: Int) -> Tree {
    let prio = prio_of();
    node(lo, hi, Int::ZERO, prio, None, None)
}

/// `t` moved by d: O(1), copying the root.
pub(super) fn moved(t: &Tree, d: &Int) -> Tree {
    let n = t.as_deref()?;
    if d.is_zero() {
        return t.clone();
    }
    let off = &n.off + d;
    node(
        n.lo.clone(),
        n.hi.clone(),
        off,
        n.prio,
        n.left.clone(),
        n.right.clone(),
    )
}

/// The intervals of `t` whose lower end is below k, and the others: O(log n) expected,
/// copying the path it walks.
fn split(t: &Tree, k: &Int) -> (Tree, Tree) {
    let Some(n) = t else {
        return (None, None);
    };
    let neg = -&n.off;
    if &(&n.lo + &n.off) < k {
        let (a, b) = split(&moved(&n.right, &n.off), k);
        let right = moved(&a, &neg);
        (
            node(
                n.lo.clone(),
                n.hi.clone(),
                n.off.clone(),
                n.prio,
                n.left.clone(),
                right,
            ),
            b,
        )
    } else {
        let (a, b) = split(&moved(&n.left, &n.off), k);
        let left = moved(&b, &neg);
        (
            a,
            node(
                n.lo.clone(),
                n.hi.clone(),
                n.off.clone(),
                n.prio,
                left,
                n.right.clone(),
            ),
        )
    }
}

/// The intervals of `a` and then of `b`, every one of `a` below every one of `b`:
/// O(log n) expected.
fn join(a: Tree, b: Tree) -> Tree {
    let (x, y) = match (a, b) {
        (None, t) | (t, None) => return t,
        (Some(x), Some(y)) => (x, y),
    };
    if x.prio >= y.prio {
        let right = join(moved(&x.right, &x.off), Some(y));
        let right = moved(&right, &-&x.off);
        node(
            x.lo.clone(),
            x.hi.clone(),
            x.off.clone(),
            x.prio,
            x.left.clone(),
            right,
        )
    } else {
        let left = join(Some(x), moved(&y.left, &y.off));
        let left = moved(&left, &-&y.off);
        node(
            y.lo.clone(),
            y.hi.clone(),
            y.off.clone(),
            y.prio,
            left,
            y.right.clone(),
        )
    }
}

/// The first or the last interval of `t`: O(log n) expected.
fn end(t: &Tree, last: bool) -> Option<(Int, Int)> {
    let mut n = t.as_deref()?;
    let mut off = n.off.clone();
    while let Some(c) = if last {
        n.right.as_deref()
    } else {
        n.left.as_deref()
    } {
        n = c;
        off = &off + &n.off;
    }
    Some((&n.lo + &off, &n.hi + &off))
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
    let mut at = t.as_deref();
    let mut off = Int::ZERO;
    let mut hit = false;
    while let Some(n) = at {
        off = &off + &n.off;
        if &n.lo + &off <= *r {
            hit = &n.hi + &off > *r;
            at = n.right.as_deref();
        } else {
            at = n.left.as_deref();
        }
    }
    hit
}

/// Pushes the intervals of `t` on `out` in order: O(n).
fn push_all(t: &Tree, off: &Int, out: &mut Vec<(Int, Int)>) {
    if let Some(n) = t {
        let off = off + &n.off;
        push_all(&n.left, &off, out);
        out.push((&n.lo + &off, &n.hi + &off));
        push_all(&n.right, &off, out);
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
            let done = self.done.take();
            let cur = self.cur.take().and_then(|(a, b)| single(a, b));
            self.done = join(join(done, cur), body);
            self.cur = Some((lo, hi));
        }
    }

    fn finish(self) -> Tree {
        join(self.done, self.cur.and_then(|(a, b)| single(a, b)))
    }
}

/// The union of `a` and `b`, intervals that meet or touch fused.
// Complexity tradeoff: merging the two lists is O(|a| + |b|), which makes a chain of steps
// quadratic. Here each maximal run of one set's intervals in the merged order moves whole
// by a split and a join, and each fused interval costs one split: O((r + f) log n) expected
// for r runs and f fusions. The bound over a chain is at `Shift::apply`.
pub(super) fn union(mut a: Tree, mut b: Tree) -> Tree {
    if a.is_none() {
        return b;
    }
    if b.is_none() {
        return a;
    }
    let mut out = Merge {
        done: None,
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
    match (x, y) {
        (None, None) => true,
        (Some(x), Some(y)) => Arc::ptr_eq(x, y),
        _ => false,
    }
}

impl Node {
    /// The intervals of the subtree, in the frame of its parent.
    fn listed(&self) -> Vec<(Int, Int)> {
        let mut out = Vec::new();
        push_all(&self.left, &self.off, &mut out);
        out.push((&self.lo + &self.off, &self.hi + &self.off));
        push_all(&self.right, &self.off, &mut out);
        out
    }
}

/// Two roots are equal when they hold the same intervals, whatever their shapes: O(n).
impl PartialEq for Node {
    fn eq(&self, other: &Node) -> bool {
        self.listed() == other.listed()
    }
}

impl Eq for Node {}

impl std::fmt::Debug for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.listed()).finish()
    }
}
