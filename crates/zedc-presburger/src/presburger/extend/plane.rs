//! The integer hull of a conjunction of linear rows over at most two symbols, kept up to date
//! row by row (LOAD-chain-move-tangent: design B of the cross-review XR-load-call-node,
//! /home/luke/Work/wt/design-b22-load5.md section 1, with the decisions H1-H4 of its META3).
//!
//! The hull H is the convex hull of the integer points where every row holds. It is in one of
//! five states (design G3): Empty; a Point; a Line (a point, a primitive direction and an
//! integer range of the parameter, either end unbounded); a Band (a primitive normal `n` and
//! `lo <= n . p <= hi`, either end unbounded: the plane, a half-plane or a strip); or a pointed
//! Polygon of positive area, bounded (a cycle of sides) or unbounded (a path of sides between
//! two end rays). An integer point is in H exactly when every row holds there, since H is the
//! hull of those points and lies inside the region of the rows. So the conjunction holds
//! somewhere iff H is not Empty, and its negation holds somewhere iff H is not the plane; each
//! answer comes with a point (step 7), and the solver decides nothing (META3 H2).
//!
//! A row is added by the transition of the state. A Polygon goes through Harvey's steps:
//! 1. the row `a x + b y >= c` is tightened to `a/g x + b/g y >= ceil(c/g)`, `g = gcd(a, b)`;
//! 2. the positions of largest and least `f = a x + b y` are found by one descent each;
//! 3. the run, the positions with `f <= c` (ties in the run, META3 H3), by binary searches on
//!    the stretches where `f` is monotone;
//! 4. the sides with both ends in the run go, by splits;
//! 5. Harvey's cuts between the side `e_p` before the run and `e_q` after it, case 1 when the
//!    new line holds an integer point between them and case 2 when not (Harvey section 5);
//! 6. the cuts are joined in, at most three sides are checked for redundancy, and the
//!    dimension is checked when at most two old positions are kept (META3 H1);
//! 7. the witnesses of both polarities, read when asked.
//!
//! Persistence: the sides are a join-based AVL tree with path copying, so a new version shares
//! every untouched node with the old, which stays valid: a conjunction extended by many callers
//! costs each the same, with no amortization (META1, error 2).
//!
//! Cost of a row added to a hull of N sides whose rows have coefficients of at most A in
//! absolute value: O(log N + log A) arithmetic operations, worst case (proof at [`Plane::with`]).
//!
//! Prior work. W. Harvey, "Computing two-dimensional integer hulls", SIAM J. Comput. 28(6),
//! 2285-2299, 1999, doi:10.1137/S009753979528977X: the tightening, the integer hull of the
//! corner of two rows by continued fractions (section 4), the cases of an added row (section 5,
//! p. 2291), at most three redundancy checks ("These are Ci-1, Ci+1, and Ci'", p. 2291), and
//! Theorem 6.12, "Incrementally computing the integer hull of n inequalities with largest
//! magnitude coefficient A_max is O(n log A_max)", a bound amortized over one sequence of
//! insertions into one tree; here each row is worst case O(log N + log A), since the run is
//! found by binary search and removed by splits instead of one side at a time. The corner hull
//! follows the convergent construction of the hull of the lattice points under a line (the
//! article "Continued fractions", section "Convex hull under the line", cp-algorithms.com,
//! read 2026-11-24), checked against the O(A) walk of the cross-review's prototype
//! (`proto-r3/hull.rs`, `pairwise`; here `tests::pairwise_walk`). Path copying: J. R. Driscoll,
//! N. Sarnak, D. D. Sleator and R. E. Tarjan, "Making data structures persistent", J. Comput.
//! Syst. Sci. 38(1), 86-124, 1989, doi:10.1016/0022-0000(89)90034-2, p. 116. Join and split:
//! G. E. Blelloch, D. Ferizovic and Y. Sun, "Just join for parallel ordered sets", SPAA 2016,
//! doi:10.1145/2935764.2935768: the AVL join in O(|h(l) - h(r)| + 1) and split in O(log n). An
//! online hull with worst-case O(log n) insertion: F. P. Preparata, "An optimal real-time
//! algorithm for planar convex hulls", Communications of the ACM 22(7), 402-405, 1979,
//! doi:10.1145/359131.359132 (points, not half-planes, and no integer hull). Static algorithms,
//! one region at a time and so Θ(n) a link here: Eisenbrand and Laue's linear-time integer
//! programming in the plane (F. Eisenbrand and S. Laue, "A linear algorithm for integer
//! programming in the plane", Mathematical Programming 102(2), 249-259, 2005,
//! doi:10.1007/s10107-004-0520-0; not read in full), and Mukherjee's 2D integer hulls (C.
//! Mukherjee, "A new algorithm for computing integer hulls of 2D polyhedral sets",
//! arXiv:2509.09134, 2025). Rows of two variables with unit coefficients only (UTVPI) have an
//! incremental test of O(n + m log m) for each row added (A. Schutt and P. J. Stuckey,
//! "Incremental satisfiability and implication for UTVPI constraints", arXiv:0709.2961, 2007;
//! INFORMS J. Computing, 2010), which the rows here, with any coefficients, do not meet;
//! integer feasibility of rows that each read two of many variables, with any coefficients, is
//! NP-complete (J. C. Lagarias, "The computational complexity of simultaneous Diophantine
//! approximation problems", SIAM J. Comput. 14(1), 196-209, 1985, doi:10.1137/0214016; not read
//! in full), so the restriction here to two symbols in all is what makes a polynomial bound
//! possible. The flatness route (a thin region has its integer points on few lattice lines)
//! needs the lattice width of the region, which has no incremental method; its constant
//! 1 + 2/√3 in the plane is Hurkens' (C. A. J. Hurkens, "Blowing up convex sets in the plane",
//! Linear Algebra and its Applications 134, 121-128, 1990, doi:10.1016/0024-3795(90)90010-a).
//!
//! Design A, which this replaces, kept the rows that bound the region over Q and decided them
//! whole: Θ(n) a link on the tangent chain, 38.3 times the instructions from 50 to 400 links.

use std::cmp::Ordering;
use std::collections::HashMap;
use std::sync::Arc;

use super::super::formula::Rel;
use super::super::{Atom, Con, Formula, Id};
use super::counts;
use zedc_int::int::Int;

/// A point with integer coordinates.
type P = (Int, Int);
/// A rational point `(x / d, y / d)`, `d > 0`.
type Q = (Int, Int, Int);

fn int(v: i64) -> Int {
    Int::from(v)
}

fn cross(u: &P, v: &P) -> Int {
    &(&u.0 * &v.1) - &(&u.1 * &v.0)
}

fn dot(u: &P, v: &P) -> Int {
    &(&u.0 * &v.0) + &(&u.1 * &v.1)
}

fn neg(u: &P) -> P {
    (-&u.0, -&u.1)
}

fn sign(v: &Int) -> i64 {
    if v.is_positive() {
        1
    } else if v.is_negative() {
        -1
    } else {
        0
    }
}

/// The row `a x + b y >= c`; `(a, b)` is the inward normal.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Row {
    a: Int,
    b: Int,
    c: Int,
}

impl Row {
    fn n(&self) -> P {
        (self.a.clone(), self.b.clone())
    }

    fn f(&self, p: &P) -> Int {
        &(&self.a * &p.0) + &(&self.b * &p.1)
    }

    fn holds(&self, p: &P) -> bool {
        self.f(p) >= self.c
    }

    /// The direction of travel along the side, counterclockwise around the region.
    fn dir(&self) -> P {
        (self.b.clone(), -&self.a)
    }

    /// Whether the rational point `q` is in the half-plane.
    fn holds_q(&self, q: &Q) -> bool {
        &(&self.a * &q.0) + &(&self.b * &q.1) >= &self.c * &q.2
    }

    /// An integer point on the line `a x + b y = c` of the row tightened (`gcd(a, b) = 1`).
    fn bezout(&self) -> P {
        point_on(&self.n(), &self.c)
    }

    /// Whether `o` bounds this row's line from the other side.
    fn opposite(&self, o: &Row) -> bool {
        self.a == -&o.a && self.b == -&o.b && (&self.c + &o.c).is_zero()
    }
}

/// An integer point with `n . p = k`, `n` primitive: `s n.0 + t n.1 = 1` by Bézout.
fn point_on(n: &P, k: &Int) -> P {
    let (_, s, t) = n.0.bezout(&n.1);
    (&s * k, &t * k)
}

/// Step 1 (design D1): `a x + b y >= c` with `g = gcd(a, b) > 0` is `a/g x + b/g y >= ceil(c/g)`
/// over the integers, since the left side is a multiple of `g` at every integer point. O(1).
fn tighten(a: Int, b: Int, c: Int) -> Row {
    let g = a.gcd(&b);
    Row {
        a: a.div_floor(&g),
        b: b.div_floor(&g),
        c: c.div_ceil(&g),
    }
}

/// Where the lines of `r` and `s` meet, by Cramer's rule; `None` when they are parallel.
fn meet(r: &Row, s: &Row) -> Option<Q> {
    let d = &(&r.a * &s.b) - &(&s.a * &r.b);
    if d.is_zero() {
        return None;
    }
    let x = &(&r.c * &s.b) - &(&s.c * &r.b);
    let y = &(&r.a * &s.c) - &(&s.a * &r.c);
    Some(if d.is_negative() {
        (-&x, -&y, -&d)
    } else {
        (x, y, d)
    })
}

fn integral(q: &Q) -> Option<P> {
    (q.0.mod_floor(&q.2).is_zero() && q.1.mod_floor(&q.2).is_zero())
        .then(|| (q.0.div_floor(&q.2), q.1.div_floor(&q.2)))
}

/// 0 for the half-turn from `base` (its own direction included), 1 for the other.
fn half(base: &P, v: &P) -> u8 {
    let c = cross(base, v);
    if c.is_positive() || (c.is_zero() && dot(base, v).is_positive()) {
        0
    } else {
        1
    }
}

/// Whether `v` is strictly after `w` counterclockwise from `base`, `base` itself first.
fn after(base: &P, v: &P, w: &P) -> bool {
    let (hv, hw) = (half(base, v), half(base, w));
    if hv != hw {
        return hv > hw;
    }
    cross(w, v).is_positive()
}

/// A value of `f` on the boundary: a vertex's, or the limit along an end ray.
#[derive(Clone, Debug)]
enum Ext {
    NegInf,
    /// `n / d`, `d > 0`.
    Fin(Int, Int),
    PosInf,
}

fn ext_cmp(x: &Ext, y: &Ext) -> Ordering {
    let rank = |e: &Ext| match e {
        Ext::NegInf => 0,
        Ext::Fin(..) => 1,
        Ext::PosInf => 2,
    };
    match (x, y) {
        (Ext::Fin(a, b), Ext::Fin(c, d)) => (a * d).cmp(&(c * b)),
        _ => rank(x).cmp(&rank(y)),
    }
}

/// `x` against the finite `c`.
fn vs(x: &Ext, c: &Int) -> Ordering {
    ext_cmp(x, &Ext::Fin(c.clone(), int(1)))
}

// ---- the persistent sequence of sides ----

type S = Arc<Row>;
type Tree = Option<Arc<Node>>;

/// A node of the join-based AVL tree of sides, in sequence order. Each node holds the first
/// and last side of its subtree, so that the side before any node is read in O(1) during a
/// descent: the last of its left subtree, or the side of the ancestor the descent last went
/// right from.
#[derive(Debug)]
struct Node {
    side: S,
    left: Tree,
    right: Tree,
    height: u32,
    size: usize,
    first: S,
    last: S,
}

fn height(t: &Tree) -> u32 {
    t.as_ref().map_or(0, |n| n.height)
}

fn size(t: &Tree) -> usize {
    t.as_ref().map_or(0, |n| n.size)
}

/// A new node, counted with every node read ([`counts::HULL_NODES`], META3 H3).
fn mk(l: Tree, s: S, r: Tree) -> Tree {
    counts::add(counts::HULL_NODES, 1);
    let first = l.as_ref().map_or_else(|| s.clone(), |n| n.first.clone());
    let last = r.as_ref().map_or_else(|| s.clone(), |n| n.last.clone());
    Some(Arc::new(Node {
        height: 1 + height(&l).max(height(&r)),
        size: size(&l) + size(&r) + 1,
        side: s,
        left: l,
        right: r,
        first,
        last,
    }))
}

fn parts(n: &Arc<Node>) -> (Tree, S, Tree) {
    (n.left.clone(), n.side.clone(), n.right.clone())
}

fn rot_left(t: Tree) -> Tree {
    let n = t.expect("a rotation of a node");
    let (l, s, r) = parts(&n);
    let rn = r.expect("a left rotation has a right child");
    let (rl, rs, rr) = parts(&rn);
    mk(mk(l, s, rl), rs, rr)
}

fn rot_right(t: Tree) -> Tree {
    let n = t.expect("a rotation of a node");
    let (l, s, r) = parts(&n);
    let ln = l.expect("a right rotation has a left child");
    let (ll, ls, lr) = parts(&ln);
    mk(ll, ls, mk(lr, s, r))
}

/// `l`, then `s`, then `r`, as one balanced tree: Blelloch, Ferizovic and Sun's AVL join (SPAA
/// 2016, Figure 2). It descends the taller tree's spine to the height of the shorter, making
/// O(|h(l) - h(r)| + 1) nodes, and rebalances with at most two rotations at each level it
/// returns through; their Lemma 1 shows the result is an AVL tree of height at most
/// `max(h(l), h(r)) + 1`.
fn join(l: Tree, s: S, r: Tree) -> Tree {
    if height(&l) > height(&r) + 1 {
        join_right(l, s, r)
    } else if height(&r) > height(&l) + 1 {
        join_left(l, s, r)
    } else {
        mk(l, s, r)
    }
}

fn join_right(l: Tree, s: S, r: Tree) -> Tree {
    let n = l.expect("the taller tree is not empty");
    let (ll, ls, lr) = parts(&n);
    let t = if height(&lr) <= height(&r) + 1 {
        let t = mk(lr, s, r);
        if height(&t) > height(&ll) + 1 {
            return rot_left(mk(ll, ls, rot_right(t)));
        }
        t
    } else {
        join_right(lr, s, r)
    };
    if height(&t) <= height(&ll) + 1 {
        mk(ll, ls, t)
    } else {
        rot_left(mk(ll, ls, t))
    }
}

fn join_left(l: Tree, s: S, r: Tree) -> Tree {
    let n = r.expect("the taller tree is not empty");
    let (rl, rs, rr) = parts(&n);
    let t = if height(&rl) <= height(&l) + 1 {
        let t = mk(l, s, rl);
        if height(&t) > height(&rr) + 1 {
            return rot_right(mk(rot_left(t), rs, rr));
        }
        t
    } else {
        join_left(l, s, rl)
    };
    if height(&t) <= height(&rr) + 1 {
        mk(t, rs, rr)
    } else {
        rot_right(mk(t, rs, rr))
    }
}

/// `l` then `r`. O(log(|l| + |r|) + 1): one split of the last side off `l`, one join.
fn join2(l: Tree, r: Tree) -> Tree {
    if l.is_none() {
        return r;
    }
    if r.is_none() {
        return l;
    }
    let k = size(&l);
    let (a, b) = split_at(&l, k - 1);
    let last = b.expect("the last side").side.clone();
    join(a, last, r)
}

/// The first `i` sides and the rest. O(log n): the joins on the way back up take pieces of
/// increasing height, and their costs `|h(a) - h(b)| + 1` telescope to O(h(t)) (Blelloch,
/// Ferizovic and Sun, SPAA 2016, the bound of split).
fn split_at(t: &Tree, i: usize) -> (Tree, Tree) {
    let Some(n) = t else {
        return (None, None);
    };
    counts::add(counts::HULL_NODES, 1);
    let ls = size(&n.left);
    if i <= ls {
        let (a, b) = split_at(&n.left, i);
        (a, join(b, n.side.clone(), n.right.clone()))
    } else {
        let (a, b) = split_at(&n.right, i - ls - 1);
        (join(n.left.clone(), n.side.clone(), a), b)
    }
}

/// A balanced tree of `v`, in order. O(|v|).
fn from_slice(v: &[S]) -> Tree {
    if v.is_empty() {
        return None;
    }
    let m = v.len() / 2;
    mk(from_slice(&v[..m]), v[m].clone(), from_slice(&v[m + 1..]))
}

/// The side at index `i < size(t)`. O(log n).
fn get(t: &Tree, mut i: usize) -> &S {
    let mut node = t.as_ref().expect("an index in range");
    loop {
        counts::add(counts::HULL_NODES, 1);
        let ls = size(&node.left);
        match i.cmp(&ls) {
            Ordering::Less => node = node.left.as_ref().expect("an index in range"),
            Ordering::Equal => return &node.side,
            Ordering::Greater => {
                i -= ls + 1;
                node = node.right.as_ref().expect("an index in range");
            }
        }
    }
}

/// The sides in order. O(n).
fn to_vec(t: &Tree, out: &mut Vec<S>) {
    if let Some(n) = t {
        counts::add(counts::HULL_NODES, 1);
        to_vec(&n.left, out);
        out.push(n.side.clone());
        to_vec(&n.right, out);
    }
}

fn first(t: &Tree) -> Option<&S> {
    t.as_ref().map(|n| &n.first)
}

fn last(t: &Tree) -> Option<&S> {
    t.as_ref().map(|n| &n.last)
}

/// The least index `i` in `lo..hi` at which `pred(before, side)` holds, `before` the side at
/// `i - 1` (`wrap` at 0), when `pred` is false and then true along `lo..hi`. One descent: an
/// index below `lo` acts as false and one at or past `hi` as true, which keeps the order
/// false-then-true over all indices, so each node sends the descent one way. O(log n).
fn search(
    t: &Tree,
    lo: usize,
    hi: usize,
    wrap: Option<&S>,
    pred: &mut dyn FnMut(Option<&Row>, &Row) -> bool,
) -> Option<usize> {
    let mut node = t.as_ref();
    let mut base = 0;
    let mut before: Option<S> = wrap.cloned();
    let mut best = None;
    while let Some(n) = node {
        counts::add(counts::HULL_NODES, 1);
        let i = base + size(&n.left);
        let go_left = if i < lo {
            false
        } else if i >= hi {
            true
        } else {
            let prev = match &n.left {
                Some(l) => Some(&*l.last),
                None => before.as_deref(),
            };
            if pred(prev, &n.side) {
                best = Some(i);
                true
            } else {
                false
            }
        };
        if go_left {
            node = n.left.as_ref();
        } else {
            before = Some(n.side.clone());
            base = i + 1;
            node = n.right.as_ref();
        }
    }
    best
}

// ---- the five states ----

#[derive(Clone, Debug)]
enum Hull {
    Empty,
    Point(P),
    /// `p0 + t d`, `d` primitive, `lo <= t <= hi`, a missing end unbounded.
    Line {
        p0: P,
        d: P,
        lo: Option<Int>,
        hi: Option<Int>,
    },
    /// `lo <= n . p <= hi`, `n` primitive; the plane when both ends are missing.
    Band {
        n: P,
        lo: Option<Int>,
        hi: Option<Int>,
    },
    /// The sides counterclockwise. Bounded: a cycle, the first side the one whose normal has the
    /// least angle from angle 0 (the seam). Unbounded: a path, the first side holding the
    /// incoming end ray and the last the outgoing one.
    Poly {
        sides: Tree,
        bounded: bool,
    },
}

/// The mutants of the tests: each disables one step, and a test shows each is caught. Off
/// outside the tests.
pub(super) mod mutant {
    #[cfg(test)]
    pub(crate) const NONE: u8 = 0;
    /// Ties out of the run (`f < c`), META3 H3.
    pub(crate) const TIES_OUT: u8 = 1;
    /// No Harvey cuts: the new row is joined in as it is.
    pub(crate) const NO_CUTS: u8 = 2;
    /// Case 1 taken in case 2.
    pub(crate) const CASE1_IN_CASE2: u8 = 3;
    /// No dimension check (META3 H1).
    pub(crate) const NO_COLLAPSE: u8 = 4;
    /// The run found by reading every position (the cost control of design D14).
    pub(crate) const SCAN: u8 = 5;
    #[cfg(test)]
    thread_local! {
        pub(crate) static ON: std::cell::Cell<u8> = const { std::cell::Cell::new(NONE) };
    }
}

fn mutant_on(m: u8) -> bool {
    #[cfg(test)]
    {
        mutant::ON.with(|c| c.get() == m)
    }
    #[cfg(not(test))]
    {
        let _ = m;
        false
    }
}

fn line_of(r: &Row) -> Hull {
    Hull::Line {
        p0: r.bezout(),
        d: r.dir(),
        lo: None,
        hi: None,
    }
}

/// A Line or Band with equal ends drops a dimension; with crossed ends it is Empty.
fn norm(h: Hull) -> Hull {
    match h {
        Hull::Line {
            p0,
            d,
            lo: Some(l),
            hi: Some(u),
        } if l == u => Hull::Point((&p0.0 + &(&l * &d.0), &p0.1 + &(&l * &d.1))),
        Hull::Line {
            lo: Some(l),
            hi: Some(u),
            ..
        } if l > u => Hull::Empty,
        Hull::Band {
            n,
            lo: Some(l),
            hi: Some(u),
        } if l == u => line_of(&Row {
            a: n.0,
            b: n.1,
            c: l,
        }),
        Hull::Band {
            lo: Some(l),
            hi: Some(u),
            ..
        } if l > u => Hull::Empty,
        h => h,
    }
}

/// The row `a x + b y >= c` added to `h`, by the transitions of design G3. `None` only where an
/// invariant the proofs rest on fails (two adjacent sides parallel, a case 2 without both
/// neighbors); the caller then decides the conjunction by the solver, so a broken invariant
/// costs time, never a wrong answer. Cost: O(1) for every state but a Polygon, whose cost is
/// [`poly`]'s.
fn add(h: &Hull, a: Int, b: Int, c: Int) -> Option<Hull> {
    if a.is_zero() && b.is_zero() {
        return Some(if c.is_positive() {
            Hull::Empty
        } else {
            h.clone()
        });
    }
    add_row(h, &tighten(a, b, c))
}

fn add_row(h: &Hull, u: &Row) -> Option<Hull> {
    let c = &u.c;
    Some(match h {
        Hull::Empty => Hull::Empty,
        Hull::Point(p) if u.holds(p) => h.clone(),
        Hull::Point(_) => Hull::Empty,
        Hull::Line { p0, d, lo, hi } => {
            // u at p0 + t d is u.f(p0) + s t >= c.
            let (s, r) = (dot(&u.n(), d), c - &u.f(p0));
            let (lo, hi) = (lo.clone(), hi.clone());
            norm(match sign(&s) {
                0 if !r.is_positive() => h.clone(),
                0 => Hull::Empty,
                1 => {
                    let v = r.div_ceil(&s);
                    Hull::Line {
                        p0: p0.clone(),
                        d: d.clone(),
                        lo: Some(lo.map_or(v.clone(), |l| l.max(v))),
                        hi,
                    }
                }
                _ => {
                    let v = r.div_floor(&s);
                    Hull::Line {
                        p0: p0.clone(),
                        d: d.clone(),
                        lo,
                        hi: Some(hi.map_or(v.clone(), |x| x.min(v))),
                    }
                }
            })
        }
        Hull::Band {
            lo: None, hi: None, ..
        } => Hull::Band {
            n: u.n(),
            lo: Some(c.clone()),
            hi: None,
        },
        Hull::Band { n, lo, hi } if u.n() == *n => norm(Hull::Band {
            n: n.clone(),
            lo: Some(lo.clone().map_or(c.clone(), |l| l.max(c.clone()))),
            hi: hi.clone(),
        }),
        Hull::Band { n, lo, hi } if u.n() == neg(n) => norm(Hull::Band {
            n: n.clone(),
            lo: lo.clone(),
            hi: Some(hi.clone().map_or(-c, |x| x.min(-c))),
        }),
        Hull::Band { n, lo, hi } => {
            // Oblique: a pointed Polygon, a path, the walls before u and after it; step 5
            // repairs each new corner.
            let walls = [
                lo.as_ref().map(|l| Row {
                    a: n.0.clone(),
                    b: n.1.clone(),
                    c: l.clone(),
                }),
                hi.as_ref().map(|x| Row {
                    a: -&n.0,
                    b: -&n.1,
                    c: -x,
                }),
            ];
            let un = u.n();
            let side = |before: bool| -> Vec<S> {
                (walls.iter().flatten())
                    .filter(|w| cross(&w.n(), &un).is_positive() == before)
                    .map(|w| Arc::new(w.clone()))
                    .collect()
            };
            return assemble(
                from_slice(&side(true)),
                from_slice(&side(false)),
                u,
                false,
                true,
            );
        }
        Hull::Poly { sides, bounded } => return poly(sides, *bounded, u),
    })
}

/// The boundary of a Polygon read against `f = u.n . p`. Positions: on a cycle, `0..k`, position
/// `j` the vertex where side `j - 1` (side `k - 1` for `j = 0`) meets side `j`; on a path,
/// `0..=k`, position 0 the far end of the incoming ray, `j` in `1..k` the vertex where side
/// `j - 1` meets side `j`, and `k` the far end of the outgoing ray.
struct Boundary<'a> {
    sides: &'a Tree,
    bounded: bool,
    u: &'a Row,
    k: usize,
    /// Set when two adjacent sides are parallel, which a Polygon never has.
    bad: std::cell::Cell<bool>,
}

impl Boundary<'_> {
    fn np(&self) -> usize {
        if self.bounded { self.k } else { self.k + 1 }
    }

    fn at(&self, prev: Option<&Row>, side: &Row) -> Ext {
        match prev.and_then(|p| meet(p, side)) {
            Some(q) => Ext::Fin(&(&self.u.a * &q.0) + &(&self.u.b * &q.1), q.2),
            None => {
                self.bad.set(true);
                Ext::NegInf
            }
        }
    }

    /// `f` along an end ray of direction `d` from the vertex of value `v`.
    fn ray(&self, d: &P, v: impl FnOnce() -> Ext) -> Ext {
        match sign(&dot(&self.u.n(), d)) {
            1 => Ext::PosInf,
            -1 => Ext::NegInf,
            _ => v(),
        }
    }

    /// `f` at position `p`. O(log k).
    fn f(&self, p: usize) -> Ext {
        let k = self.k;
        if !self.bounded && p == 0 {
            let s0 = first(self.sides).expect("a path has sides");
            return self.ray(&neg(&s0.dir()), || self.f(1));
        }
        if !self.bounded && p == k {
            let sl = last(self.sides).expect("a path has sides");
            return self.ray(&sl.dir(), || self.f(k - 1));
        }
        let prev = if p == 0 {
            last(self.sides).expect("a cycle has sides")
        } else {
            get(self.sides, p - 1)
        };
        self.at(Some(prev), get(self.sides, p))
    }

    /// The least offset `i < len` with `pred` true at position `from + i` (modulo the positions
    /// on a cycle), `pred` false and then true along them. O(log k): at most two descents, and
    /// the two ray ends read directly.
    fn first(&self, from: usize, len: usize, pred: &dyn Fn(&Ext) -> bool) -> Option<usize> {
        let k = self.k;
        let mut p = |prev: Option<&Row>, side: &Row| pred(&self.at(prev, side));
        if self.bounded {
            let wrap = last(self.sides);
            let end = (from + len).min(k);
            if let Some(i) = search(self.sides, from, end, wrap, &mut p) {
                return Some(i - from);
            }
            let more = (from + len).saturating_sub(k);
            return search(self.sides, 0, more, wrap, &mut p).map(|i| k - from + i);
        }
        let to = from + len; // exclusive, at most k + 1
        if from == 0 && pred(&self.f(0)) {
            return Some(0);
        }
        if let Some(i) = search(self.sides, from.max(1), to.min(k), None, &mut p) {
            return Some(i - from);
        }
        (to == k + 1 && pred(&self.f(k))).then(|| k - from)
    }

    /// Step 2 (design D2): the position of the largest `f` (`sign` 1) or the least (`sign` -1).
    /// With `t = -sign u.n`, the extreme vertex is the one whose two sides' normals have `t`
    /// between them, so it starts the first side whose normal is after `t` counterclockwise
    /// from the seam: angle 0 on a cycle, whose normals grow from there, and the first normal
    /// on a path, whose normals grow over less than a half-turn. A path's end rays are read
    /// first: one along which `f` grows without bound is the largest. One descent, O(log k).
    fn extreme(&self, sign: i64) -> usize {
        let k = self.k;
        let t = (&int(-sign) * &self.u.a, &int(-sign) * &self.u.b);
        if !self.bounded {
            let infinite = |e: &Ext| match e {
                Ext::PosInf => sign > 0,
                Ext::NegInf => sign < 0,
                Ext::Fin(..) => false,
            };
            if infinite(&self.f(0)) {
                return 0;
            }
            if infinite(&self.f(k)) {
                return k;
            }
            let base = first(self.sides).expect("a path has sides").n();
            let mut after_t = |_: Option<&Row>, s: &Row| after(&base, &s.n(), &t);
            let j = search(self.sides, 0, k, None, &mut after_t).unwrap_or(k);
            return j.clamp(1, k - 1);
        }
        let base = (int(1), int(0));
        let mut after_t = |_: Option<&Row>, s: &Row| after(&base, &s.n(), &t);
        search(self.sides, 0, k, None, &mut after_t).unwrap_or(k) % k
    }
}

/// Step 3: the run, the positions with `f <= c` (ties in the run, META3 H3), as intervals of
/// positions: one cyclic interval on a cycle, at most two on a path. On a cycle `f` falls from
/// the largest position to the least and rises back; on a path it is monotone on each of the
/// at most three stretches the two cut. So each end of the run is the first position of a
/// stretch where `f <= c` turns true or false, one binary search ([`Boundary::first`]).
/// O(log k).
fn run(b: &Boundary, imax: usize, imin: usize, c: &Int) -> Vec<(usize, usize)> {
    let ties_out = mutant_on(mutant::TIES_OUT);
    let inr = move |e: &Ext| match vs(e, c) {
        Ordering::Less => true,
        Ordering::Equal => !ties_out,
        Ordering::Greater => false,
    };
    let np = b.np();
    let len = |from: usize, to: usize| (to + np - from) % np + 1;
    if b.bounded {
        let (Some(d), Some(u)) = (
            b.first(imax, len(imax, imin), &inr),
            b.first(imin, len(imin, imax), &|e| !inr(e)),
        ) else {
            b.bad.set(true);
            return vec![];
        };
        return vec![((imax + d) % np, (imin + u + np - 1) % np)];
    }
    let (p, q) = (imax.min(imin), imax.max(imin));
    let mut out: Vec<(usize, usize)> = vec![];
    for (from, to) in [(0, p), (p, q), (q, np - 1)] {
        let rising = ext_cmp(&b.f(to), &b.f(from)) != Ordering::Less;
        let n = to - from + 1;
        let (s, e) = if rising {
            match b.first(from, n, &|e| !inr(e)) {
                Some(0) => continue,
                Some(j) => (from, from + j - 1),
                None => (from, to),
            }
        } else {
            match b.first(from, n, &inr) {
                Some(j) => (from + j, to),
                None => continue,
            }
        };
        match out.last_mut() {
            Some(l) if l.1 + 1 >= s => l.1 = l.1.max(e),
            _ => out.push((s, e)),
        }
    }
    out
}

/// The run by reading every position with a literal `<=`: the oracle of the tie test (META3
/// H3), never mutated, and the run of the mutant `SCAN`, the cost control of design D14.
/// O(k log k).
fn run_by_scan(b: &Boundary, c: &Int) -> Vec<(usize, usize)> {
    let np = b.np();
    let mut out: Vec<(usize, usize)> = vec![];
    for p in 0..np {
        if vs(&b.f(p), c) != Ordering::Greater {
            match out.last_mut() {
                Some(l) if l.1 + 1 == p => l.1 = p,
                _ => out.push((p, p)),
            }
        }
    }
    if b.bounded && out.len() == 2 && out[0].0 == 0 && out[1].1 == np - 1 {
        let tail = out.pop().expect("two intervals");
        out[0].0 = tail.0;
    }
    out
}

/// Steps 2-6 on a pointed Polygon of k sides. O(log k + log A): two descents for the extremes,
/// at most six searches for the run, a constant number of splits and joins, each O(log k), and
/// [`assemble`]'s O(log A + log k).
fn poly(sides: &Tree, bounded: bool, u: &Row) -> Option<Hull> {
    let c = &u.c;
    let k = size(sides);
    let b = Boundary {
        sides,
        bounded,
        u,
        k,
        bad: std::cell::Cell::new(false),
    };
    let (imax, imin) = (b.extreme(1), b.extreme(-1));
    let (fmax, fmin) = (b.f(imax), b.f(imin));
    if b.bad.get() {
        return None;
    }
    if vs(&fmin, c) != Ordering::Less {
        return Some(Hull::Poly {
            sides: sides.clone(),
            bounded,
        });
    }
    match vs(&fmax, c) {
        Ordering::Less => return Some(Hull::Empty),
        Ordering::Equal => return face(sides, bounded, k, imax, u),
        Ordering::Greater => {}
    }
    let runs = if mutant_on(mutant::SCAN) {
        run_by_scan(&b, c)
    } else {
        run(&b, imax, imin, c)
    };
    let np = b.np();
    if b.bad.get() || runs.is_empty() || runs.len() > 2 {
        return None;
    }
    let in_run: usize = runs.iter().map(|&(s, e)| (e + np - s) % np + 1).sum();
    if in_run >= np {
        return None;
    }
    let collapse = np - in_run <= 2;
    if bounded {
        // The run s..=e: sides s..e-1 have both ends in it and go; e_q is side e and e_p side
        // s - 1, and the kept cycle is sides e..s-1, cyclically.
        let (s, e) = runs[0];
        let cycle = if s <= e {
            join2(split_at(sides, e).1, split_at(sides, s).0)
        } else {
            split_at(&split_at(sides, s).0, e).1
        };
        return assemble(cycle, None, u, true, collapse);
    }
    if let [(0, q0), (q1, last)] = runs[..] {
        if last != k {
            return None;
        }
        // Both end rays in the run: the middle sides stay and the new row closes the cycle.
        let mid = split_at(&split_at(sides, q1).0, q0).1;
        return assemble(mid, None, u, true, collapse);
    }
    if runs.len() != 1 {
        return None;
    }
    let (p0, p1) = runs[0];
    let pre = split_at(sides, p0).0;
    let post = split_at(sides, p1).1;
    assemble(pre, post, u, false, collapse)
}

/// The hull meets the line `f = c` only where `f` is largest, at `imax`: the side there whose
/// normal is `-u`, cut by its neighbors (a Line), or else the vertex (a Point). O(log k).
fn face(sides: &Tree, bounded: bool, k: usize, imax: usize, u: &Row) -> Option<Hull> {
    let (sa, sb) = if bounded {
        ((imax + k - 1) % k, imax)
    } else {
        (imax - 1, imax)
    };
    for j in [sa, sb] {
        let sj = get(sides, j);
        if sj.n() != neg(&u.n()) {
            continue;
        }
        let mut l = line_of(sj);
        let nb: Vec<usize> = if bounded {
            vec![(j + k - 1) % k, (j + 1) % k]
        } else {
            [j.checked_sub(1), (j + 1 < k).then_some(j + 1)]
                .into_iter()
                .flatten()
                .collect()
        };
        for i in nb {
            l = add_row(&l, get(sides, i))?;
        }
        return Some(l);
    }
    let prev = if imax == 0 {
        last(sides)?
    } else {
        get(sides, imax - 1)
    };
    let q = meet(prev, get(sides, imax))?;
    Some(integral(&q).map_or(Hull::Empty, Hull::Point))
}

/// Step 5's result.
enum Step5 {
    /// The sides between `e_p` and `e_q`, in order, and the third side step 6 checks.
    Sides(Vec<Row>, Row),
    /// A case-2 cut on `e_q`'s line from the other side: every integer point is on it.
    Line(Row),
}

/// Whether the line of `c` holds an integer point where `ep` and `eq` hold (case 1): the
/// parameter range on the line, its two ends rounded inward (design G4). O(1).
fn section_has_point(c: &Row, ep: Option<&Row>, eq: Option<&Row>) -> bool {
    let p0 = c.bezout();
    let d = c.dir();
    let (mut lo, mut hi): (Option<Int>, Option<Int>) = (None, None);
    for r in [ep, eq].into_iter().flatten() {
        // r at p0 + t d: s t >= r.c - r.f(p0).
        let s = dot(&r.n(), &d);
        let k = &r.c - &r.f(&p0);
        match sign(&s) {
            1 => {
                let v = k.div_ceil(&s);
                lo = Some(lo.map_or(v.clone(), |o| o.max(v)));
            }
            -1 => {
                let v = k.div_floor(&s);
                hi = Some(hi.map_or(v.clone(), |o| o.min(v)));
            }
            _ if k.is_positive() => return false,
            _ => {}
        }
    }
    match (lo, hi) {
        (Some(l), Some(h)) => l <= h,
        _ => true,
    }
}

/// Whether `s` is redundant between its neighbors `r` and `t`: they meet at an angle below 180
/// degrees, at a point where `s` holds. O(1).
fn redundant_between(r: &Row, s: &Row, t: &Row) -> bool {
    cross(&r.n(), &t.n()).is_positive() && meet(r, t).is_some_and(|q| s.holds_q(&q))
}

/// Step 5 (design G4; Harvey section 5, p. 2291): case 1 adds the corner hulls of `e_p` with C
/// and of C with `e_q`, each only where the corner is below 180 degrees; case 2 adds the cuts of
/// the corner hull of `e_p` and C from `e_p` inward until one, C', makes C redundant, then the
/// corner hull of C' and `e_q`. O(log A): each corner hull is O(log A) ([`pairwise`]), and the
/// case-2 test after each cut is O(1).
fn step5(ep: Option<&Row>, c: &Row, eq: Option<&Row>) -> Option<Step5> {
    if mutant_on(mutant::NO_CUTS) {
        return Some(Step5::Sides(vec![c.clone()], c.clone()));
    }
    let corner = |r: Option<&Row>, s: Option<&Row>| -> Vec<Row> {
        match (r, s) {
            (Some(r), Some(s)) if cross(&r.n(), &s.n()).is_positive() => pairwise(r, s),
            _ => vec![],
        }
    };
    if mutant_on(mutant::CASE1_IN_CASE2) || section_has_point(c, ep, eq) {
        counts::add(counts::HULL_CASE1, 1);
        let mut out = corner(ep, Some(c));
        out.push(c.clone());
        out.extend(corner(Some(c), eq));
        return Some(Step5::Sides(out, c.clone()));
    }
    counts::add(counts::HULL_CASE2, 1);
    let (ep, eq) = (ep?, eq?);
    if !cross(&ep.n(), &c.n()).is_positive() {
        return None;
    }
    let mut out = vec![];
    for cp in pairwise(ep, c) {
        if cp.opposite(eq) {
            return Some(Step5::Line(cp));
        }
        out.push(cp.clone());
        if redundant_between(&cp, c, eq) {
            if cross(&cp.n(), &eq.n()).is_positive() {
                out.extend(pairwise(&cp, eq));
            }
            return Some(Step5::Sides(out, cp));
        }
    }
    out.push(c.clone());
    Some(Step5::Sides(out, c.clone()))
}

/// Harvey's corner hull of `e` and `c` (`e` then `c` counterclockwise, `beta = cross(e.n, c.n)
/// > 0`, both tightened): the sides of the integer hull of the corner from `e`'s last integer
/// point to `c`'s first, in order.
///
/// The change of basis of Harvey's section 4: `X = a x + b y - e.c`, `Y = -t x + s y` with
/// `s a + t b = 1` (unimodular, so it maps the lattice onto itself and keeps the orientation)
/// makes `e` the row `X >= 0` and `c` the row `alpha X + beta Y >= gamma`, `alpha = c.a s + c.b
/// t`, `gamma = c.c - alpha e.c`; `gcd(alpha, beta) = 1`, as `c` is tightened and the change is
/// unimodular. `X*`, the least `X >= 0` with an integer point on `c`, solves `alpha X* = gamma
/// (mod beta)`, so `X* < beta`, and `X* = 0` when the corner is an integer point, which needs
/// no cut. With `u = X* - X`, `v = Y - Y*` (`(X*, Y*)` that point on `c`), the integer points
/// are those with `beta v >= alpha u`, and the cuts are the lower hull of those with `0 <= u <=
/// X*`, from `u = X*` (on `e`) to `u = 0` (on `c`). Mirrored (`w = -v`) and sheared (`w' = w + m
/// u`, `m = ceil(alpha / beta)`, unimodular), it is the upper hull of the lattice points under
/// the line `w' = r u`, `r = (m beta - alpha) / beta` in `[0, 1)`, for `0 <= u <= X*`, which
/// the convergents of `r` give ([`under_line`]).
///
/// O(log A) arithmetic operations: the continued fraction of `r` has O(log beta) terms (Lamé),
/// `beta <= 2 A^2`, and [`under_line`] makes O(1) steps for each convergent and each hull
/// vertex, of which there are O(log A) (Harvey section 4).
fn pairwise(e: &Row, c: &Row) -> Vec<Row> {
    let beta = cross(&e.n(), &c.n());
    let (_, s, t) = e.a.bezout(&e.b);
    let alpha = &(&c.a * &s) + &(&c.b * &t);
    let gamma = &c.c - &(&alpha * &e.c);
    // X* = gamma alpha^-1 mod beta.
    let (_, inv, _) = alpha.bezout(&beta);
    let xs = (&gamma * &inv).mod_floor(&beta);
    if xs.is_zero() {
        return vec![];
    }
    let ys = (&gamma - &(&alpha * &xs)).div_floor(&beta);
    let m = alpha.div_ceil(&beta);
    let num = &(&m * &beta) - &alpha;
    // (u, w') to (X, Y): X = X* - u, Y = Y* + v = Y* + m u - w'.
    let pts: Vec<P> = (under_line(&num, &beta, &xs).into_iter().rev())
        .map(|(u, w)| (&xs - &u, &(&ys + &(&m * &u)) - &w))
        .collect();
    corner_rows(e, &pts)
}

/// The rows of the edges of the chain `pts` of the corner of `e` (in the coordinates `X`, `Y`
/// of [`pairwise`], `X` growing), in `x` and `y`, tightened, equal neighbors once. O(|pts|).
fn corner_rows(e: &Row, pts: &[P]) -> Vec<Row> {
    let (_, s, t) = e.a.bezout(&e.b);
    let mut out: Vec<Row> = vec![];
    for w in pts.windows(2) {
        let ((x1, y1), (x2, y2)) = (&w[0], &w[1]);
        if x1 == x2 && y1 == y2 {
            continue;
        }
        // aa X + bb Y >= aa x1 + bb y1: the hull on the left of (x1, y1) to (x2, y2).
        let (aa, bb) = (-&(y2 - y1), x2 - x1);
        let k = &(&aa * x1) + &(&bb * y1);
        // X = a x + b y - e.c, Y = -t x + s y.
        let r = tighten(
            &(&aa * &e.a) - &(&bb * &t),
            &(&aa * &e.b) + &(&bb * &s),
            &k + &(&aa * &e.c),
        );
        if out.last() != Some(&r) {
            out.push(r);
        }
    }
    out
}

/// The vertices `(x, y)` of the upper hull of the lattice points with `0 <= x <= n` and `y <=
/// (p / q) x`, `0 <= p < q`, `gcd(p, q) = 1`, from `(0, 0)` to `x = n`, a vertex possibly
/// repeated. The convergents of `p / q` (cp-algorithms, "Continued fractions", "Convex hull
/// under the line", function `hull`): each edge is a multiple of a semiconvergent from below,
/// `p_{i-1} + t p_i` over `q_{i-1} + t q_i` with `i` odd in the list that starts `p_-2, p_-1`,
/// the largest `t` that fits, as many copies as fit. At the first odd `i`, `q_{i-1} = q_0 = 1`,
/// so the walk reaches `x = n`. O(log q) steps: one for each convergent and each edge.
fn under_line(p: &Int, q: &Int, n: &Int) -> Vec<P> {
    let (mut a, mut b) = (p.clone(), q.clone());
    let (mut ps, mut qs) = (vec![int(0), int(1)], vec![int(1), int(0)]);
    while !b.is_zero() {
        let t = a.div_floor(&b);
        let r = &a - &(&t * &b);
        let l = ps.len();
        ps.push(&(&t * &ps[l - 1]) + &ps[l - 2]);
        qs.push(&(&t * &qs[l - 1]) + &qs[l - 2]);
        (a, b) = (b, r);
    }
    let (lp, lq) = (ps[ps.len() - 1].clone(), qs[qs.len() - 1].clone());
    let t = n.div_floor(&lq);
    let mut hp = vec![int(0), &t * &lp];
    let mut hq = vec![int(0), &t * &lq];
    for i in (1..qs.len()).rev().filter(|i| i % 2 == 1) {
        while qs[i].is_positive() && &hq[hq.len() - 1] + &qs[i - 1] <= *n {
            let x = hq[hq.len() - 1].clone();
            let y = hp[hp.len() - 1].clone();
            let t = (&(n - &x) - &qs[i - 1]).div_floor(&qs[i]);
            let dp = &ps[i - 1] + &(&t * &ps[i]);
            let dq = &qs[i - 1] + &(&t * &qs[i]);
            let k = (n - &x).div_floor(&dq);
            hp.push(&y + &(&k * &dp));
            hq.push(&x + &(&k * &dq));
        }
    }
    hq.into_iter().zip(hp).collect()
}

/// Steps 5 and 6. A path: the new sides go between `pre`, ending with `e_p`, and `post`,
/// starting with `e_q`. A cycle (`closed`): `pre` is the kept cycle from `e_q` to `e_p`, and
/// the new sides close it. Step 6 checks `e_p`, `e_q` and the third side (C or C') against
/// their neighbors (Harvey p. 2291), all inside a window of the two sides at each end and the q
/// new ones, so the checks and the window cost O(q + 1); the window is cut out and joined back
/// by O(1) splits and joins, O(log k) each. The dimension check (META3 H1) runs only when at
/// most two old positions are kept (`collapse`): three kept vertices of a convex polygon are not
/// collinear, so H stays two-dimensional, and the area stays positive with them; then H has at
/// most three old sides besides the q new ones, read in O(q + 1).
fn assemble(pre: Tree, post: Tree, c: &Row, closed: bool, collapse: bool) -> Option<Hull> {
    let (ep, eq) = if closed {
        (last(&pre).cloned(), first(&pre).cloned())
    } else {
        (last(&pre).cloned(), first(&post).cloned())
    };
    let (new, third) = match step5(ep.as_deref(), c, eq.as_deref())? {
        Step5::Line(cp) => {
            // Every integer point is on e_q's line, from C to the side after e_q (the start of
            // e_q's segment is in the run). Any old row holds on H, so cutting by more is exact.
            counts::add(counts::HULL_COLLAPSE, 1);
            let mut cut: Vec<S> = vec![Arc::new(c.clone())];
            cut.extend(ep.iter().cloned());
            let after_eq = if closed { &pre } else { &post };
            if size(after_eq) >= 2 {
                cut.push(get(after_eq, 1).clone());
            }
            let mut l = line_of(&cp);
            for r in cut {
                l = add_row(&l, &r)?;
            }
            return Some(l);
        }
        Step5::Sides(s, t) => (s, t),
    };
    let new: Vec<S> = new.into_iter().map(Arc::new).collect();
    // The window, and the trees before and after it; on a small cycle the window is all of it.
    let (before, mut window, after_, cyclic) = if closed {
        let k = size(&pre);
        let mut w = vec![];
        if k >= 4 {
            let (head, rest) = split_at(&pre, 2);
            let (middle, tail) = split_at(&rest, k - 4);
            to_vec(&tail, &mut w);
            w.extend(new.iter().cloned());
            to_vec(&head, &mut w);
            (middle, w, None, false)
        } else {
            to_vec(&pre, &mut w);
            w.extend(new.iter().cloned());
            (None, w, None, true)
        }
    } else {
        let (pre_rest, tail) = split_at(&pre, size(&pre).saturating_sub(2));
        let (head, post_rest) = split_at(&post, 2.min(size(&post)));
        let mut w = vec![];
        to_vec(&tail, &mut w);
        w.extend(new.iter().cloned());
        to_vec(&head, &mut w);
        (pre_rest, w, post_rest, false)
    };
    let rest = size(&before) + size(&after_);
    let (has_before, has_after) = match (closed, cyclic) {
        (true, false) => (true, true),
        _ => (before.is_some(), after_.is_some()),
    };
    for s in [ep, eq, Some(Arc::new(third))].into_iter().flatten() {
        let Some(i) = window.iter().position(|r| **r == *s) else {
            continue;
        };
        let m = window.len();
        if m + rest <= 3 {
            break;
        }
        let (pi, ni) = if cyclic {
            ((i + m - 1) % m, (i + 1) % m)
        } else if (i == 0 && has_before) || (i + 1 == m && has_after) {
            // Each checked side has two window sides around it but a path's end side.
            return None;
        } else if i == 0 || i + 1 == m {
            continue; // an end ray's side stays
        } else {
            (i - 1, i + 1)
        };
        if redundant_between(&window[pi], &s, &window[ni]) {
            window.remove(i);
        }
    }
    if collapse && !mutant_on(mutant::NO_COLLAPSE) {
        let mut all: Vec<S> = vec![];
        to_vec(&before, &mut all);
        all.extend(window.iter().cloned());
        to_vec(&after_, &mut all);
        if let Some(h) = collapsed(&all, closed)? {
            counts::add(counts::HULL_COLLAPSE, 1);
            return Some(h);
        }
    }
    let w = from_slice(&window);
    if closed {
        return Some(Hull::Poly {
            sides: seam(join2(before, w)),
            bounded: true,
        });
    }
    Some(Hull::Poly {
        sides: join2(join2(before, w), after_),
        bounded: false,
    })
}

/// The dimension check (META3 H1, design G3/G5): `Some(Some(h))` when the sides `all` (a cycle
/// when `closed`) bound a set of no area, `h` its Line or Point; `Some(None)` when the area is
/// positive. A convex set of no area lies on one line L, and at a point of its relative
/// interior every side through that point has its normal along L's, or it would cut the set
/// there, and sides from both hands meet there, or the set would have area near it; the sides
/// are tightened, so two of them are opposite on L ([`Row::opposite`]), found by a hash of the
/// normals, O(m) for m sides. The Line is then L cut by every side, O(m). Otherwise the set is
/// a Point only when it is bounded (a cycle) and every vertex is that one integer point: a path
/// has two end rays, so it is never a Point (Codex B1: a quadrant cut by `x >= 5` keeps one
/// vertex and two rays, and stays a Polygon).
fn collapsed(all: &[S], closed: bool) -> Option<Option<Hull>> {
    let by: HashMap<P, &Row> = all.iter().map(|r| (r.n(), &**r)).collect();
    let pair = (all.iter()).find(|r| by.get(&neg(&r.n())).is_some_and(|o| r.opposite(o)));
    if let Some(r) = pair {
        let mut l = line_of(r);
        for s in all {
            l = add_row(&l, s)?;
        }
        return Some(Some(l));
    }
    if !closed {
        return Some(None);
    }
    let m = all.len();
    let mut point: Option<P> = None;
    for i in 0..m {
        let p = integral(&meet(&all[(i + m - 1) % m], &all[i])?)?;
        match &point {
            Some(o) if *o != p => return Some(None),
            _ => point = Some(p),
        }
    }
    Some(point.map(Hull::Point))
}

/// The cycle `t` turned to start at its side of least angle from angle 0. The sides run
/// counterclockwise from some side, so the angle from angle 0 grows along them and drops once,
/// at the seam: the first side whose normal comes before the first side's. One descent, a split
/// and a join, O(log k).
fn seam(t: Tree) -> Tree {
    let k = size(&t);
    let Some(f) = first(&t).map(|s| s.n()) else {
        return t;
    };
    let base = (int(1), int(0));
    let mut before_first = |_: Option<&Row>, s: &Row| after(&base, &f, &s.n());
    match search(&t, 1, k, None, &mut before_first) {
        Some(i) => {
            let (a, b) = split_at(&t, i);
            join2(b, a)
        }
        None => t,
    }
}

impl Hull {
    /// An integer point of H (step 7, Claude R3 item 3): a vertex of a Polygon, the Point, an
    /// end or the base of a Line, a point on a bound of a Band. O(log k).
    fn inside(&self) -> Option<P> {
        match self {
            Hull::Empty => None,
            Hull::Point(p) => Some(p.clone()),
            Hull::Line { p0, d, lo, hi } => {
                let t = lo.clone().or_else(|| hi.clone()).unwrap_or_else(|| int(0));
                Some((&p0.0 + &(&t * &d.0), &p0.1 + &(&t * &d.1)))
            }
            Hull::Band { n, lo, hi } => Some(match lo.as_ref().or(hi.as_ref()) {
                Some(k) => point_on(n, k),
                None => (int(0), int(0)),
            }),
            Hull::Poly { sides, bounded } => {
                let r = if *bounded {
                    last(sides)?
                } else {
                    first(sides)?
                };
                let s = if *bounded {
                    first(sides)?
                } else {
                    get(sides, 1)
                };
                integral(&meet(r, s)?)
            }
        }
    }

    /// An integer point outside H, `None` for the plane (step 7, Claude R3 item 3). A Polygon:
    /// the vertex [`Hull::inside`] gives, on the first side `(a', b')`, moved by `-sign(a')`
    /// along x, or by `-sign(b')` along y when `a' = 0`, lowers that side's row by `|a'|` or
    /// `|b'|`, so the row fails there. O(log k).
    fn outside(&self) -> Option<P> {
        match self {
            Hull::Empty => Some((int(0), int(0))),
            Hull::Point(p) => Some((&p.0 + &int(1), p.1.clone())),
            Hull::Line { p0, d, .. } => Some((&p0.0 - &d.1, &p0.1 + &d.0)),
            Hull::Band { n, lo, hi } => match (lo, hi) {
                (Some(l), _) => Some(point_on(n, &(l - &int(1)))),
                (None, Some(h)) => Some(point_on(n, &(h + &int(1)))),
                (None, None) => None,
            },
            Hull::Poly { sides, .. } => {
                let v = self.inside()?;
                let s = first(sides)?;
                Some(if s.a.is_zero() {
                    (v.0, &v.1 - &int(sign(&s.b)))
                } else {
                    (&v.0 - &int(sign(&s.a)), v.1)
                })
            }
        }
    }

    /// The number of rows that state H: the sides of a Polygon (the root's size, design B), the
    /// bounds of a Band, the line and the bounds of a Line, two lines for a Point. O(1).
    fn rows(&self) -> usize {
        match self {
            Hull::Empty => 1,
            Hull::Point(_) => 2,
            Hull::Line { lo, hi, .. } => 1 + lo.is_some() as usize + hi.is_some() as usize,
            Hull::Band { lo, hi, .. } => lo.is_some() as usize + hi.is_some() as usize,
            Hull::Poly { sides, .. } => size(sides),
        }
    }
}

/// The integer hull of a conjunction of rows `>=` over at most two symbols, `axes`, the first
/// axis the one named first.
#[derive(Clone, Debug)]
pub(crate) struct Plane {
    axes: [Option<Atom>; 2],
    hull: Hull,
}

impl Plane {
    /// The plane: no row yet.
    fn all() -> Plane {
        Plane {
            axes: [None, None],
            hull: Hull::Band {
                n: (int(1), int(0)),
                lo: None,
                hi: None,
            },
        }
    }

    /// The hull of `f`, a conjunction of rows `>=` over at most two symbols; `None` for any
    /// other formula. Each of its n rows is added in turn, O(log n + log A) each ([`Plane::with`]),
    /// and each distinct conjunction under it is read once. Counted ([`counts::PLANE_FRESH`]).
    pub(crate) fn of(f: &Formula) -> Option<Plane> {
        let mut plane = Plane::all();
        let mut seen = std::collections::HashSet::new();
        let mut stack = vec![f];
        while let Some(g) = stack.pop() {
            match g {
                Formula::Con(c) => plane.add(c)?,
                Formula::And(_) if seen.insert(Id::any(g)) => stack.extend(g.kids()),
                Formula::And(_) => {}
                _ => return None,
            }
        }
        counts::add(counts::PLANE_FRESH, 1);
        Some(plane)
    }

    /// This hull with the rows `cons` added, a new version sharing the unchanged nodes, this one
    /// unchanged; `None` when one is not a row `>=` over the two axes. Each row is counted
    /// ([`counts::HULL_UPDATES`]).
    ///
    /// Cost of a row, H of N sides with coefficients at most A: O(log N + log A) arithmetic
    /// operations, worst case. Proof: the transitions of every state but a Polygon are O(1)
    /// (a Band made oblique is a path of at most two walls and the cuts of step 5). On a
    /// Polygon, step 2 is two descents of the tree, of height O(log N) (AVL); step 3 is at most
    /// three stretches, each one or two descents; step 4 is at most four splits and a join,
    /// O(log N) each (Blelloch, Ferizovic and Sun); step 5 makes at most three corner hulls of
    /// O(log A) sides each ([`pairwise`]); step 6 builds a window of q + 4 sides, q = O(log A),
    /// checks three, and joins it back with two joins, O(q + log N); the dimension check, when
    /// it runs, reads at most q + 3 sides; the seam is one descent, a split and a join. Every
    /// bound is worst case: nothing is amortized, so a hull extended by any number of callers
    /// costs each the same.
    pub(crate) fn with<'a>(&self, cons: impl IntoIterator<Item = &'a Con>) -> Option<Plane> {
        let mut plane = self.clone();
        for c in cons {
            counts::add(counts::HULL_UPDATES, 1);
            plane.add(c)?;
        }
        Some(plane)
    }

    /// The number of rows that state the hull ([`Hull::rows`]). O(1).
    pub(crate) fn rows(&self) -> usize {
        self.hull.rows()
    }

    /// Whether the conjunction holds somewhere: H is not Empty. O(1).
    pub(crate) fn holds(&self) -> bool {
        !matches!(self.hull, Hull::Empty)
    }

    /// Whether its negation holds somewhere: H is not the plane. O(1).
    pub(crate) fn fails(&self) -> bool {
        !matches!(
            self.hull,
            Hull::Band {
                lo: None,
                hi: None,
                ..
            }
        )
    }

    /// An integer point where the conjunction holds, as values of the axes. O(log N).
    pub(crate) fn inside(&self) -> Option<Vec<(Atom, Int)>> {
        self.hull.inside().map(|p| self.values(p))
    }

    /// An integer point where it fails. O(log N).
    pub(crate) fn outside(&self) -> Option<Vec<(Atom, Int)>> {
        self.hull.outside().map(|p| self.values(p))
    }

    /// The values of the axes named at `p`.
    fn values(&self, (x, y): P) -> Vec<(Atom, Int)> {
        (self.axes.iter().zip([x, y]))
            .filter_map(|(a, v)| a.clone().map(|a| (a, v)))
            .collect()
    }

    /// Adds the row `c`, naming its atoms as axes: `None` when `c` is not a row `>=` over
    /// symbols, or names a third.
    fn add(&mut self, c: &Con) -> Option<()> {
        if c.rel != Rel::Ge {
            return None;
        }
        let (mut a, mut b) = (int(0), int(0));
        for (atom, k) in &c.lin.terms {
            if !matches!(atom, Atom::Sym(_)) {
                return None;
            }
            let i = match &self.axes {
                [Some(x), _] if x == atom => 0,
                [_, Some(y)] if y == atom => 1,
                [None, _] => 0,
                [Some(_), None] => 1,
                [Some(_), Some(_)] => return None,
            };
            self.axes[i] = Some(atom.clone());
            *[&mut a, &mut b][i] = k.clone();
        }
        // lin >= 0 is a x + b y >= -constant.
        self.hull = add(&self.hull, a, b, -&c.lin.constant)?;
        Some(())
    }
}

#[cfg(test)]
mod tests;
