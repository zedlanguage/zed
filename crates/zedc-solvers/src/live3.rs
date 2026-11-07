//! Exact integer feasibility of rows over three variables (DESIGN.md sec:domains, step L1.38,
//! plan item LIVE3): Lenstra's method in dimension three, with no search over values and no
//! refusal.
//!
//! The rows are `a·x + k >= 0` with integer `a` and `k`. A system with an integer point has one
//! with every coordinate at most `4·Δ` in magnitude, where `Δ` bounds the subdeterminants of
//! `[a k]` (one point per minimal face and integer generators of the recession cone, each of
//! size at most `Δ` by Cramer's rule; by Carathéodory three generators suffice, and taking off
//! the whole parts of their multipliers leaves an integer point). By Hadamard's bound a minor
//! of `a` alone is at most `6·A³`, and one with a column of `k` at most `6·A²·K`, for `A` the
//! largest coefficient and `K` the largest constant, so the rows are cut to the box `|x_i| <=
//! 24·A²·max(A, K)`, which keeps every integer point that matters and makes every linear
//! program below bounded.
//!
//! 1. The real points: a linear program in three variables decides whether the rows have
//!    one, by Megiddo's prune-and-search [Megiddo 1984, sec. 4] in O(m), deterministic, with
//!    exact rationals (see `least`).
//! 2. A rounding with a fixed ratio: six linear programs give a simplex `S` of points of the
//!    rows, each vertex the farthest along a direction normal to the edges before it, and the
//!    rows lie within `g + 25·(S - g)` for `g` the center of `S`.
//! 3. LLL on the integer lattice under the quadratic form in which `S` is regular, then the
//!    nearest plane point to `g`. That point is checked against every row; if it fails, the
//!    last vector of the dual basis is a direction `u` along which the rows take fewer than
//!    `75·√7 < 199` integer values.
//! 4. Each integer value `t` of `u·x` over the rows is a slice: `u` is completed to a
//!    unimodular matrix by Euclid's algorithm, and the slice is a system over two variables,
//!    which `twovar::point` decides exactly.
//! 5. No slice has a point: the rows have none.
//!
//! The answer is complete, so it does not depend on the order of the variables; the point
//! found may.

use std::borrow::Borrow;
use std::cmp::Ordering;

use super::linear::{Q, Term};
use super::twovar;
use zedc_int::int::Int;

/// A row `a·x + k >= 0` over three variables.
pub type Row3 = ([Int; 3], Int);

fn zero() -> Q {
    Q::of(Int::ZERO)
}

fn q(n: i64) -> Q {
    Q::of(Int::from(n))
}

/// `floor(c + 1/2)`, the nearest integer to `c`.
fn nearest(c: &Q) -> Int {
    c.add(&Q::new(Int::ONE, Int::from(2))).floor()
}

/// `a + b`, with no arithmetic when either is zero.
fn plus(a: &Q, b: &Q) -> Q {
    if b.is_zero() {
        a.clone()
    } else if a.is_zero() {
        b.clone()
    } else {
        a.add(b)
    }
}

/// A number `c0 + c1·ε1 + c2·ε2` of the rationals with two infinitesimals above zero, `ε2`
/// infinitely smaller than `ε1`. Comparing the coefficients in order is the order of the
/// field. `ε1` moves a line of the plane off itself, and `ε2` a point of a line, so that a
/// value next to a line or point is compared with the value on it exactly.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct E([Q; 3]);

impl E {
    fn of(c: Q) -> E {
        E([c, zero(), zero()])
    }

    fn zero() -> E {
        E::of(zero())
    }

    // The parts of `ε1` and `ε2` are zero in most numbers, so a zero part costs no arithmetic.
    fn add(&self, o: &E) -> E {
        E([0, 1, 2].map(|i| plus(&self.0[i], &o.0[i])))
    }

    fn sub(&self, o: &E) -> E {
        E([0, 1, 2].map(|i| plus(&self.0[i], &o.0[i].neg())))
    }

    fn scale(&self, s: &Q) -> E {
        E([0, 1, 2].map(|i| {
            let c = &self.0[i];
            if c.is_zero() { zero() } else { c.mul(s) }
        }))
    }

    /// `self + s·ε_i`.
    fn nudge(&self, i: usize, s: i64) -> E {
        let mut e = self.clone();
        e.0[i] = e.0[i].add(&q(s));
        e
    }

    /// The rational part, of a number with no infinitesimal part.
    fn real(self) -> Q {
        let [a, b, c] = self.0;
        debug_assert!(
            b.is_zero() && c.is_zero(),
            "a point on a line given by rationals"
        );
        a
    }
}

/// What a point of the plane, or of a line, is worth, compared in order: the most any row is
/// violated by (at least zero), the least `z` the rows allow there, and the two coordinates.
/// The least value is the least point of `z` over the rows, the first and then the second
/// coordinate least among those, when they have a real point, and else a point of least
/// violation.
type Val = [E; 4];

/// How a group of pieces is combined: lower bounds on `z` and violations by their greatest,
/// upper bounds by their least.
#[derive(Clone, Copy)]
enum Keep {
    Max,
    Min,
}

/// The groups of pieces, in order: lower bounds on `z`, upper bounds, violations.
const KEEP: [Keep; 3] = [Keep::Max, Keep::Min, Keep::Max];

/// The affine function `g·t + h` of the parameter of a line.
#[derive(Clone)]
struct Lin1 {
    g: Q,
    h: E,
}

impl Lin1 {
    fn at(&self, t: &E) -> E {
        t.scale(&self.g).add(&self.h)
    }

    fn minus(&self, o: &Lin1) -> Lin1 {
        Lin1 {
            g: self.g.sub(&o.g),
            h: self.h.sub(&o.h),
        }
    }
}

/// The affine function `g·y + h` of a point of the plane.
#[derive(Clone)]
struct Lin2 {
    g: [Q; 2],
    h: Q,
}

impl Lin2 {
    fn at(&self, y: &[Q; 2]) -> Q {
        self.g[0].mul(&y[0]).add(&self.g[1].mul(&y[1])).add(&self.h)
    }

    fn minus(&self, o: &Lin2) -> Lin2 {
        #[cfg(feature = "counts")]
        counts::MINUS.set(counts::MINUS.get() + 1);
        Lin2 {
            g: [self.g[0].sub(&o.g[0]), self.g[1].sub(&o.g[1])],
            h: self.h.sub(&o.h),
        }
    }

    /// The function on the points `base + t·dir` of a line.
    fn on(&self, l: &Line) -> Lin1 {
        Lin1 {
            g: self.g[0].mul(&l.dir[0]).add(&self.g[1].mul(&l.dir[1])),
            h: l.base[0]
                .scale(&self.g[0])
                .add(&l.base[1].scale(&self.g[1]))
                .add(&E::of(self.h.clone())),
        }
    }
}

/// The calls of `Lin2::minus` on a thread (feature `counts`, SLABS-count). The linear programs
/// call it a bounded number of times per piece, so a test holds the count to linear growth in the
/// rows, a measure the load does not change.
#[cfg(feature = "counts")]
pub mod counts {
    use std::cell::Cell;

    thread_local! {
        pub(super) static MINUS: Cell<u64> = const { Cell::new(0) };
    }

    /// The calls of `Lin2::minus` on this thread since it started.
    pub fn minus() -> u64 {
        MINUS.get()
    }
}

/// The line of the points `base + t·dir` of the plane.
struct Line {
    base: [E; 2],
    dir: [Q; 2],
}

/// Which piece of a pair is dropped once it is known which is the greater where the least
/// value lies: the lesser of a group kept by its greatest, the greater of one kept by its
/// least.
fn loser(keep: Keep, i: usize, j: usize, i_greater: bool) -> usize {
    match (keep, i_greater) {
        (Keep::Max, true) | (Keep::Min, false) => j,
        (Keep::Max, false) | (Keep::Min, true) => i,
    }
}

/// Removes the pieces marked in `drop`, in each group.
fn retain<T>(p: &mut [Vec<T>; 3], drop: &[Vec<bool>; 3]) {
    for (grp, d) in p.iter_mut().zip(drop) {
        let mut at = 0;
        grp.retain(|_| {
            at += 1;
            !d[at - 1]
        });
    }
}

/// A piecewise linear function of the parameter at a point: its value, and its slopes to the
/// right and to the left, owned or borrowed from the pieces.
struct At<S> {
    v: E,
    right: S,
    left: S,
}

impl<S: Borrow<Q>> At<S> {
    /// The greatest of `fs`, or the least with `keep` `Min`, at `t`: the slope to the right
    /// is the greatest (least) slope among the pieces that take that value, and to the left the
    /// least (greatest).
    fn of(fs: impl Iterator<Item = At<S>>, keep: Keep) -> Option<At<S>> {
        fs.reduce(|a, b| {
            let o = match keep {
                Keep::Max => a.v.cmp(&b.v),
                Keep::Min => b.v.cmp(&a.v),
            };
            match o {
                Ordering::Greater => a,
                Ordering::Less => b,
                Ordering::Equal => {
                    let hi = |x: S, y: S| {
                        if x.borrow() >= y.borrow() {
                            (x, y)
                        } else {
                            (y, x)
                        }
                    };
                    let (r, l) = match keep {
                        Keep::Max => (hi(a.right, b.right).0, hi(a.left, b.left).1),
                        Keep::Min => (hi(a.right, b.right).1, hi(a.left, b.left).0),
                    };
                    At {
                        v: a.v,
                        right: r,
                        left: l,
                    }
                }
            }
        })
    }

    fn owned(self) -> At<Q> {
        At {
            v: self.v,
            right: self.right.borrow().clone(),
            left: self.left.borrow().clone(),
        }
    }
}

/// The value of the point `t` of the line `l` under the pieces `p`, and its slopes to the
/// right and left, part by part. `t` has no part of `ε2`, so the value at `t ± ε2` is the
/// value at `t` plus `±ε2` times these slopes, and is compared with it by the first slope that
/// is not zero.
fn eval1(p: &[Vec<Lin1>; 3], l: &Line, t: &E) -> (Val, [Q; 4], [Q; 4]) {
    // The slopes are borrowed from the pieces until a group's greatest or least is known.
    let at = |g: usize| {
        p[g].iter().map(|f| At {
            v: f.at(t),
            right: &f.g,
            left: &f.g,
        })
    };
    let lo = At::of(at(0), Keep::Max).expect("a lower bound").owned();
    let up = At::of(at(1), Keep::Min).expect("an upper bound");
    let gap = At {
        v: lo.v.sub(&up.v),
        right: lo.right.sub(up.right),
        left: lo.left.sub(up.left),
    };
    let none = At {
        v: E::zero(),
        right: zero(),
        left: zero(),
    };
    let worst = At::of(
        [gap, none]
            .into_iter()
            .chain(At::of(at(2), Keep::Max).map(At::owned)),
        Keep::Max,
    )
    .expect("a violation");
    let y0 = l.base[0].add(&t.scale(&l.dir[0]));
    let y1 = l.base[1].add(&t.scale(&l.dir[1]));
    let [d0, d1] = l.dir.clone();
    (
        [worst.v, lo.v, y0, y1],
        [worst.right, lo.right, d0.clone(), d1.clone()],
        [worst.left, lo.left, d0, d1],
    )
}

/// The value of the point `t` of the line `l` under the pieces `p`.
fn value1(p: &[Vec<Lin1>; 3], l: &Line, t: &E) -> Val {
    eval1(p, l, t).0
}

/// Whether the value falls moving by `+ε2` along slopes `d`: the first slope not zero is
/// negative.
fn falls(d: &[Q; 4]) -> bool {
    d.iter().find(|s| !s.is_zero()).is_some_and(Q::is_negative)
}

/// The least value on the line `l` and its parameter, by prune-and-search: the pieces of each
/// group are paired, the median of the points where two of a pair meet is tried, and on the
/// side away from the least value one piece of each pair whose meeting point lies there is
/// dropped, since the other is above it (or below it) wherever the least value can lie. The
/// value is convex in the order of [`Val`], so the least value lies to the side where a point
/// infinitely near the median is worth less, or at the median when neither side is. Each round
/// drops a quarter of the pieces, so the work is O(m).
fn solve1(mut p: [Vec<Lin1>; 3], l: &Line) -> (E, Val) {
    loop {
        let mut drop: [Vec<bool>; 3] = [0, 1, 2].map(|g| vec![false; p[g].len()]);
        let mut dropped = false;
        let mut meets: Vec<(E, usize, usize, usize)> = Vec::new();
        for (gi, grp) in p.iter().enumerate() {
            for i in (0..grp.len() / 2).map(|i| 2 * i) {
                let (a, b) = (&grp[i], &grp[i + 1]);
                let dg = a.g.sub(&b.g);
                if dg.is_zero() {
                    drop[gi][loser(KEEP[gi], i, i + 1, a.h >= b.h)] = true;
                    dropped = true;
                } else {
                    let t = b.h.sub(&a.h).scale(&Q::of(Int::ONE).div(&dg));
                    meets.push((t, gi, i, i + 1));
                }
            }
        }
        if meets.is_empty() {
            if !dropped {
                return least1(&p, l);
            }
        } else {
            let mid = meets.len() / 2;
            meets.select_nth_unstable_by(mid, |a, b| a.0.cmp(&b.0));
            let t = meets[mid].0.clone();
            let (v, right, left) = eval1(&p, l, &t);
            let side = if falls(&right) {
                Ordering::Greater
            } else if falls(&left.map(|s| s.neg())) {
                Ordering::Less
            } else {
                return (t, v);
            };
            for (m, gi, i, j) in &meets {
                // The least value lies strictly beyond a meeting point on the far side of the
                // median, or at it.
                if m.cmp(&t) == side.reverse() || *m == t {
                    let rising = p[*gi][*i].g > p[*gi][*j].g;
                    drop[*gi][loser(KEEP[*gi], *i, *j, rising == side.is_gt())] = true;
                }
            }
        }
        retain(&mut p, &drop);
    }
}

/// The least value on a line where each group has one piece at most: it lies where two of
/// `0`, the lower bound less the upper bound, and the violation meet, since elsewhere the
/// value falls along the line one way or the other.
fn least1(p: &[Vec<Lin1>; 3], l: &Line) -> (E, Val) {
    let mut ks = vec![
        Lin1 {
            g: zero(),
            h: E::zero(),
        },
        p[0][0].minus(&p[1][0]),
    ];
    ks.extend(p[2].first().cloned());
    let mut best: Option<(E, Val)> = None;
    for (i, a) in ks.iter().enumerate() {
        for b in &ks[i + 1..] {
            let dg = a.g.sub(&b.g);
            if dg.is_zero() {
                continue;
            }
            let t = b.h.sub(&a.h).scale(&Q::of(Int::ONE).div(&dg));
            let v = value1(p, l, &t);
            if best.as_ref().is_none_or(|(_, w)| v < *w) {
                best = Some((t, v));
            }
        }
    }
    best.expect("the least value on a line lies where two pieces meet")
}

/// The least value on the line `n·y = c + s·ε1`, and its point.
fn on_line(p: &[Vec<Lin2>; 3], n: &[Q; 2], c: &Q, s: i64) -> ([E; 2], Val) {
    let c = E::of(c.clone()).nudge(1, s);
    let base = if n[0].is_zero() {
        [E::zero(), c.scale(&Q::of(Int::ONE).div(&n[1]))]
    } else {
        [c.scale(&Q::of(Int::ONE).div(&n[0])), E::zero()]
    };
    let l = Line {
        base,
        dir: [n[1].neg(), n[0].clone()],
    };
    let r = [0, 1, 2].map(|g| p[g].iter().map(|f| f.on(&l)).collect());
    let (t, v) = solve1(r, &l);
    let y = [
        l.base[0].add(&t.scale(&l.dir[0])),
        l.base[1].add(&t.scale(&l.dir[1])),
    ];
    (y, v)
}

/// The point and value of the least value of the plane, found on a line tried. It ends one linear
/// program, so it is boxed to keep the results that carry it small.
type Found = Box<([Q; 2], Val)>;

/// The side of the line `n·y = c` the least value of the plane lies on, `Greater` where `n·y >
/// c`, or the point and value when it lies on the line. The value is convex, so the least
/// value on a line infinitely near on one side is less than on the line exactly when the
/// least value of the plane lies on that side.
fn side(p: &[Vec<Lin2>; 3], n: &[Q; 2], c: &Q) -> Result<Ordering, Found> {
    let (y, v) = on_line(p, n, c, 0);
    if on_line(p, n, c, 1).1 < v {
        return Ok(Ordering::Greater);
    }
    if on_line(p, n, c, -1).1 < v {
        return Ok(Ordering::Less);
    }
    let [a, b] = y;
    Err(Box::new(([a.real(), b.real()], v)))
}

/// An open region of the plane known to hold the least value: `at` plus the positive
/// combinations of `rays` and any multiples of `along`.
struct Region {
    at: [Q; 2],
    rays: Vec<[Q; 2]>,
    along: Option<[Q; 2]>,
}

fn dot2(a: &[Q; 2], b: &[Q; 2]) -> Q {
    a[0].mul(&b[0]).add(&a[1].mul(&b[1]))
}

/// The sign `f` takes all over the region, if it takes one.
fn sign_on(f: &Lin2, r: &Region) -> Option<Ordering> {
    if r.along.as_ref().is_some_and(|w| !dot2(&f.g, w).is_zero()) {
        return None;
    }
    let at = f.at(&r.at).n.cmp(&Int::ZERO);
    let rays: Vec<Ordering> = r
        .rays
        .iter()
        .map(|d| dot2(&f.g, d).n.cmp(&Int::ZERO))
        .collect();
    for s in [Ordering::Greater, Ordering::Less] {
        let all = at != s.reverse() && rays.iter().all(|r| *r != s.reverse());
        if all && (at == s || rays.contains(&s)) {
            return Some(s);
        }
    }
    None
}

/// A line where two pieces of a group meet: `f` is the first less the second.
struct Cut {
    f: Lin2,
    g: usize,
    i: usize,
    j: usize,
}

fn median(mut xs: Vec<Q>) -> Q {
    let mid = xs.len() / 2;
    xs.select_nth_unstable(mid);
    xs.swap_remove(mid)
}

/// The side of each cut the least value lies on, for an eighth of the cuts or more, by
/// Megiddo's search in the plane with two calls of [`side`]: the cuts not of the median slope
/// are paired, one steeper with one less steep; the vertical line through the median of the
/// first coordinates of their meeting points (and of the vertical cuts) is tried, then the
/// line of the median slope through the median of the meeting points beyond it (and of the
/// cuts of the median slope). The least value then lies in a known quadrant, and a cut of a
/// pair that meets in the opposite quadrant misses it. `Err` holds the point and value when
/// the least value lies on a line tried.
fn search(p: &[Vec<Lin2>; 3], cuts: &[Cut]) -> Result<Vec<Option<Ordering>>, Found> {
    // A cut `g·y + h = 0` is the vertical `y0 = -h/g0`, or `y1 = s·y0 + t`.
    let slope = |c: &Cut| -> Option<(Q, Q)> {
        let [g0, g1] = &c.f.g;
        (!g1.is_zero()).then(|| (g0.neg().div(g1), c.f.h.neg().div(g1)))
    };
    let lines: Vec<Option<(Q, Q)>> = cuts.iter().map(slope).collect();
    let slopes: Vec<Q> = lines.iter().flatten().map(|(s, _)| s.clone()).collect();
    let sm = (!slopes.is_empty()).then(|| median(slopes));
    let mut xs: Vec<Q> = Vec::new();
    let mut steep: Vec<&(Q, Q)> = Vec::new();
    let mut flat: Vec<&(Q, Q)> = Vec::new();
    let mut level: Vec<Q> = Vec::new();
    for (c, l) in cuts.iter().zip(&lines) {
        match (l, &sm) {
            (None, _) => xs.push(c.f.h.neg().div(&c.f.g[0])),
            (Some(st), Some(m)) => match st.0.cmp(m) {
                Ordering::Greater => steep.push(st),
                Ordering::Less => flat.push(st),
                Ordering::Equal => level.push(st.1.clone()),
            },
            (Some(_), None) => unreachable!("a median slope where some cut has a slope"),
        }
    }
    // Each meeting point as its first coordinate and its height above the line of the median
    // slope through the origin.
    let meets: Vec<(Q, Q)> = steep
        .iter()
        .zip(&flat)
        .map(|((s1, t1), (s2, t2))| {
            let m = sm.as_ref().expect("a median slope where two cuts meet");
            let y0 = t2.sub(t1).div(&s1.sub(s2));
            let v = s1.sub(m).mul(&y0).add(t1);
            (y0, v)
        })
        .collect();
    xs.extend(meets.iter().map(|(y0, _)| y0.clone()));
    let a = if xs.is_empty() {
        None
    } else {
        let a = median(xs);
        let s = side(p, &[q(1), zero()], &a)?;
        Some((a, s))
    };
    let mut vs: Vec<Q> = meets
        .iter()
        .filter(|(y0, _)| a.as_ref().is_none_or(|(a, s)| y0.cmp(a) != *s))
        .map(|(_, v)| v.clone())
        .collect();
    vs.extend(level);
    let b = if vs.is_empty() {
        None
    } else {
        let m = sm.as_ref().expect("a median slope where a cut has a slope");
        let b = median(vs);
        let s = side(p, &[m.neg(), q(1)], &b)?;
        Some((b, s))
    };
    let sign = |s: &Ordering| if s.is_gt() { q(1) } else { q(-1) };
    let region = match (a, b) {
        (Some((a, sa)), Some((b, sb))) => {
            let m = sm.expect("a median slope where a cut has a slope");
            let (ka, kb) = (sign(&sa), sign(&sb));
            Region {
                at: [a.clone(), b.add(&m.mul(&a))],
                rays: vec![[ka.clone(), ka.mul(&m)], [zero(), kb]],
                along: None,
            }
        }
        (Some((a, sa)), None) => Region {
            at: [a, zero()],
            rays: vec![[sign(&sa), zero()]],
            along: Some([zero(), q(1)]),
        },
        (None, Some((b, sb))) => Region {
            at: [zero(), b],
            rays: vec![[zero(), sign(&sb)]],
            along: Some([q(1), sm.expect("a median slope where a cut has a slope")]),
        },
        (None, None) => unreachable!("a line tried where there is a cut"),
    };
    Ok(cuts.iter().map(|c| sign_on(&c.f, &region)).collect())
}

/// The least value of the plane and its point, by prune-and-search as in [`solve1`] with the
/// search of [`search`] in place of the median: each round drops a sixteenth of the pieces or
/// more, with six calls of [`solve1`], so the work is O(m).
fn solve2(mut p: [Vec<Lin2>; 3]) -> ([Q; 2], Val) {
    loop {
        let mut drop: [Vec<bool>; 3] = [0, 1, 2].map(|g| vec![false; p[g].len()]);
        let mut dropped = false;
        let mut cuts: Vec<Cut> = Vec::new();
        for (gi, grp) in p.iter().enumerate() {
            for i in (0..grp.len() / 2).map(|i| 2 * i) {
                let f = grp[i].minus(&grp[i + 1]);
                if f.g.iter().all(Q::is_zero) {
                    drop[gi][loser(KEEP[gi], i, i + 1, !f.h.is_negative())] = true;
                    dropped = true;
                } else {
                    cuts.push(Cut {
                        f,
                        g: gi,
                        i,
                        j: i + 1,
                    });
                }
            }
        }
        if cuts.is_empty() {
            if !dropped {
                return least2(&p);
            }
        } else {
            let signs = match search(&p, &cuts) {
                Ok(s) => s,
                Err(found) => return *found,
            };
            for (c, s) in cuts.iter().zip(signs) {
                if let Some(s) = s {
                    drop[c.g][loser(KEEP[c.g], c.i, c.j, s.is_gt())] = true;
                }
            }
        }
        retain(&mut p, &drop);
    }
}

/// The least value of the plane where each group has one piece at most: it lies on a line
/// where two of `0`, the lower bound less the upper bound, and the violation meet, as in
/// [`least1`].
fn least2(p: &[Vec<Lin2>; 3]) -> ([Q; 2], Val) {
    let mut ks = vec![
        Lin2 {
            g: [zero(), zero()],
            h: zero(),
        },
        p[0][0].minus(&p[1][0]),
    ];
    ks.extend(p[2].first().cloned());
    let mut best: Option<([Q; 2], Val)> = None;
    for (i, a) in ks.iter().enumerate() {
        for b in &ks[i + 1..] {
            let f = a.minus(b);
            if f.g.iter().all(Q::is_zero) {
                continue;
            }
            let (y, v) = on_line(p, &f.g, &f.h.neg(), 0);
            if best.as_ref().is_none_or(|(_, w)| v < *w) {
                let [a, b] = y;
                best = Some(([a.real(), b.real()], v));
            }
        }
    }
    best.expect("the least value of the plane lies where two pieces meet")
}

/// The least point of `f·x` over the rows and the box `bx`, as the point and its value, or
/// `None` when they have no real point. With `r` the first place where `f` is not zero and
/// `z = f·x`, each row bounds `z` below, above, or not at all, in terms of the other two
/// coordinates `y`; the least `z` over the rows is the least over `y` of the greatest lower
/// bound, where no lower bound exceeds an upper one and no other row is violated. That is the
/// least value of [`solve2`], whose first part, the greatest violation, is zero exactly when
/// the rows have a real point. Megiddo's method [Megiddo 1984] in three variables; a linear
/// program in a fixed dimension is used only here, for a part with three live variables.
fn least(rows: &[Row3], bx: &[Row3], f: &[Int; 3]) -> Option<([Q; 3], Q)> {
    let r = f.iter().position(|c| !c.is_zero()).expect("a direction");
    let [s1, s2] = match r {
        0 => [1, 2],
        1 => [0, 2],
        _ => [0, 1],
    };
    let (fr, sg) = (
        f[r].abs(),
        Int::from(if f[r].is_negative() { -1 } else { 1 }),
    );
    let mut p: [Vec<Lin2>; 3] = [Vec::new(), Vec::new(), Vec::new()];
    for (a, k) in rows.iter().chain(bx) {
        // `a·x + k` times `|f_r|`, with `x_r = (z - f_s1·y0 - f_s2·y1) / f_r`.
        let ar = &sg * &a[r];
        let c1 = &(&fr * &a[s1]) - &(&ar * &f[s1]);
        let c2 = &(&fr * &a[s2]) - &(&ar * &f[s2]);
        let k = &fr * k;
        if ar.is_zero() {
            p[2].push(Lin2 {
                g: [Q::of(-&c1), Q::of(-&c2)],
                h: Q::of(-&k),
            });
        } else {
            // `ar·z + c·y + k >= 0`: `z >= -(c·y + k) / ar` where `ar > 0`, else `z <=` it.
            let d = Q::of(-&ar);
            let l = Lin2 {
                g: [Q::of(c1).div(&d), Q::of(c2).div(&d)],
                h: Q::of(k).div(&d),
            };
            p[usize::from(ar.is_negative())].push(l);
        }
    }
    let (y, v) = solve2(p);
    let [worst, z, ..] = v;
    if worst.0[0].is_positive() {
        return None;
    }
    let z = z.real();
    let [y0, y1] = y;
    let rest = Q::of(f[s1].clone())
        .mul(&y0)
        .add(&Q::of(f[s2].clone()).mul(&y1));
    let mut x = [zero(), zero(), zero()];
    x[r] = z.sub(&rest).div(&Q::of(f[r].clone()));
    x[s1] = y0;
    x[s2] = y1;
    Some((x, z))
}

fn dot3(a: &[Int; 3], x: &[Q; 3]) -> Q {
    (0..3).fold(zero(), |s, i| s.add(&Q::of(a[i].clone()).mul(&x[i])))
}

fn sub3(a: &[Q; 3], b: &[Q; 3]) -> [Q; 3] {
    [0, 1, 2].map(|i| a[i].sub(&b[i]))
}

fn add3(a: &[Q; 3], b: &[Q; 3]) -> [Q; 3] {
    [0, 1, 2].map(|i| a[i].add(&b[i]))
}

fn cross(a: &[Q; 3], b: &[Q; 3]) -> [Q; 3] {
    [0, 1, 2].map(|i| {
        let (j, k) = ((i + 1) % 3, (i + 2) % 3);
        a[j].mul(&b[k]).sub(&a[k].mul(&b[j]))
    })
}

/// The integer multiple of `v`, not zero, whose entries have no common factor.
fn primitive(v: &[Q; 3]) -> [Int; 3] {
    let l = v.iter().fold(Int::ONE, |l, c| {
        let g = l.gcd(&c.d);
        &l.div_floor(&g) * &c.d
    });
    let n = v.clone().map(|c| &c.n * &l.div_floor(&c.d));
    let g = n.iter().fold(Int::ZERO, |g, c| g.gcd(c));
    n.map(|c| c.div_floor(&g))
}

/// What the rounding finds: no real point, an integer point of the rows, or a direction `u`
/// of few integer values (one where the rows lie in a plane normal to it), with the least and
/// greatest of `u·x` over a set that holds the real points of the rows.
enum Shape {
    Empty,
    Point([Int; 3]),
    Dir([Int; 3], Q, Q),
}

/// A simplex of real points of the rows: `v0` the least of `x0`, `v1` the greatest, then for
/// `f` normal to the edges so far, the point farthest from `v0` along `f` among the least and
/// greatest of `f·x`. When the least and greatest are equal the rows lie in a plane, normal to
/// `f`. Along `f1 = e0`, `f2` and `f3` every point of the rows lies within the extent of `v1`,
/// `v2` and `v3`, and the off-diagonal entries of `f_i·(v_j - v0)` are at most the diagonal
/// ones in magnitude, so the barycentric coordinates of a point of the rows are at least `-6`
/// and the rows lie within `g + 25·(S - g)`.
fn simplex(rows: &[Row3], bx: &[Row3]) -> Result<[[Q; 3]; 4], Box<Shape>> {
    // Each vertex found is rounded to the nearest integer point, which ends the search when
    // it holds the rows.
    let lp = |f: &[Int; 3]| -> Result<Option<([Q; 3], Q)>, Box<Shape>> {
        let r = least(rows, bx, f);
        if let Some((v, _)) = &r {
            let z = v.clone().map(|c| nearest(&c));
            if holds(rows, &z) {
                return Err(Box::new(Shape::Point(z)));
            }
        }
        Ok(r)
    };
    let e0 = [Int::ONE, Int::ZERO, Int::ZERO];
    let Some((v0, lo)) = lp(&e0)? else {
        return Err(Box::new(Shape::Empty));
    };
    let neg = |f: &[Int; 3]| f.clone().map(|c| -&c);
    let (v1, hi) = lp(&neg(&e0))?.expect("a real point");
    if hi.neg() == lo {
        return Err(Box::new(Shape::Dir(e0, lo.clone(), lo)));
    }
    let d1 = sub3(&v1, &v0);
    let f2 = (0..3)
        .map(|j| {
            let mut e = [zero(), zero(), zero()];
            e[j] = q(1);
            cross(&d1, &e)
        })
        .find(|c| c.iter().any(|c| !c.is_zero()))
        .expect("a normal to an edge");
    let mut vs = vec![v0, v1];
    for f in [Some(f2), None] {
        let f =
            primitive(&f.unwrap_or_else(|| cross(&sub3(&vs[1], &vs[0]), &sub3(&vs[2], &vs[0]))));
        let (a, lo) = lp(&f)?.expect("a real point");
        let (b, hi) = lp(&neg(&f))?.expect("a real point");
        let hi = hi.neg();
        if hi == lo {
            return Err(Box::new(Shape::Dir(f, lo.clone(), lo)));
        }
        let at = dot3(&f, &vs[0]);
        let far = if hi.sub(&at) >= at.sub(&lo) { b } else { a };
        vs.push(far);
    }
    let [v0, v1, v2, v3] =
        <[[Q; 3]; 4]>::try_from(vs).unwrap_or_else(|_| unreachable!("four vertices"));
    Ok([v0, v1, v2, v3])
}

/// The inverse of the matrix whose columns are `c`, which is invertible.
fn inverse(c: &[[Q; 3]; 3]) -> [[Q; 3]; 3] {
    // Row `i` of the inverse is the cross product of the other two columns over the
    // determinant.
    let det = dot3q(&c[0], &cross(&c[1], &c[2]));
    [0, 1, 2].map(|i| cross(&c[(i + 1) % 3], &c[(i + 2) % 3]).map(|x| x.div(&det)))
}

fn dot3q(a: &[Q; 3], b: &[Q; 3]) -> Q {
    (0..3).fold(zero(), |s, i| s.add(&a[i].mul(&b[i])))
}

/// LLL on `Z³` under the quadratic form in which the simplex is regular, then the nearest
/// plane point to its center: the point when it holds every row, else the last vector of the
/// dual of the reduced basis. With `r` the inradius of the simplex in that form, the ball of
/// radius `r` about the center lies in the rows, and they lie in the ball of `75·r`; the point
/// misses a row only when `r` is below `√7/2` times the length of the last Gram–Schmidt
/// vector `b3*`, and the width of the rows along the dual vector is at most `150·r / |b3*|`,
/// below `75·√7`.
fn reduce(rows: &[Row3], s: &[[Q; 3]; 4]) -> Shape {
    let edges = [1, 2, 3].map(|i| sub3(&s[i], &s[0]));
    let m = inverse(&edges);
    // The form `Mᵀ·G·M`, with `G` twice the Gram matrix of a regular simplex of unit edges.
    let g = [[2, 1, 1], [1, 2, 1], [1, 1, 2]].map(|r| r.map(q));
    let form: [[Q; 3]; 3] = [0, 1, 2].map(|a| {
        [0, 1, 2].map(|b| {
            let mut s = zero();
            for i in 0..3 {
                for j in 0..3 {
                    s = s.add(&m[i][a].mul(&g[i][j]).mul(&m[j][b]));
                }
            }
            s
        })
    });
    let ip = |x: &[Q; 3], y: &[Q; 3]| -> Q {
        let mut s = zero();
        for i in 0..3 {
            for j in 0..3 {
                s = s.add(&x[i].mul(&form[i][j]).mul(&y[j]));
            }
        }
        s
    };
    let asq = |b: &[Int; 3]| b.clone().map(Q::of);
    let mut b: [[Int; 3]; 3] = [0, 1, 2].map(|i| [0, 1, 2].map(|j| Int::from(i64::from(i == j))));
    // The Gram–Schmidt vectors, their squared lengths, and the coefficients `mu`.
    let gs = |b: &[[Int; 3]; 3]| -> ([[Q; 3]; 3], [Q; 3], [[Q; 3]; 3]) {
        let mut st: [[Q; 3]; 3] = [0, 1, 2].map(|i| asq(&b[i]));
        let mut len: [Q; 3] = [zero(), zero(), zero()];
        let mut mu: [[Q; 3]; 3] = [0, 1, 2].map(|_| [zero(), zero(), zero()]);
        for i in 0..3 {
            for j in 0..i {
                mu[i][j] = ip(&asq(&b[i]), &st[j]).div(&len[j]);
                st[i] = sub3(&st[i], &st[j].each_ref().map(|x| x.mul(&mu[i][j])));
            }
            len[i] = ip(&st[i], &st[i]);
        }
        (st, len, mu)
    };
    let delta = Q::new(Int::from(3), Int::from(4));
    let mut k = 1;
    while k < 3 {
        for j in (0..k).rev() {
            let (_, _, mu) = gs(&b);
            let c = nearest(&mu[k][j]);
            if !c.is_zero() {
                let (low, high) = b.split_at_mut(k);
                for (x, y) in high[0].iter_mut().zip(&low[j]) {
                    *x = &*x - &(&c * y);
                }
            }
        }
        let (_, len, mu) = gs(&b);
        let m2 = mu[k][k - 1].mul(&mu[k][k - 1]);
        if len[k] >= delta.sub(&m2).mul(&len[k - 1]) {
            k += 1;
        } else {
            b.swap(k, k - 1);
            k = (k - 1).max(1);
        }
    }
    let (st, len, _) = gs(&b);
    let four = q(4);
    let center: [Q; 3] = [0, 1, 2].map(|i| s.iter().fold(zero(), |a, v| a.add(&v[i])).div(&four));
    let mut t = center.clone();
    for i in (0..3).rev() {
        let c = nearest(&ip(&t, &st[i]).div(&len[i]));
        t = sub3(&t, &asq(&b[i]).map(|x| x.mul(&Q::of(c.clone()))));
    }
    let z = sub3(&center, &t).map(|x| {
        debug_assert!(x.d == Int::ONE, "a lattice point");
        x.n
    });
    if holds(rows, &z) {
        return Shape::Point(z);
    }
    // The dual vector vanishes on `b1` and `b2` and is one on `b3`. The rows lie within
    // `g + 25·(S - g)`, which is the hull of its four vertices, so the least and greatest of
    // `u·x` there bound it over the rows, and their gap is below 199 as well: that simplex
    // lies in the ball of `75·r`.
    let cols = [0, 1, 2].map(|i| asq(&b[i]));
    let inv = inverse(&cols);
    let u = inv[2].clone().map(|x| {
        debug_assert!(x.d == Int::ONE, "a unimodular basis");
        x.n
    });
    let wide = q(25);
    let at: Vec<Q> = s
        .iter()
        .map(|v| dot3(&u, &add3(&center, &sub3(v, &center).map(|x| x.mul(&wide)))))
        .collect();
    let lo = at.iter().min().expect("four vertices").clone();
    let hi = at.iter().max().expect("four vertices").clone();
    Shape::Dir(u, lo, hi)
}

fn dot_int(a: &[Int; 3], x: &[Int; 3]) -> Int {
    (0..3).fold(Int::ZERO, |s, i| &s + &(&a[i] * &x[i]))
}

/// Whether the integer point `z` holds every row.
fn holds(rows: &[Row3], z: &[Int; 3]) -> bool {
    rows.iter()
        .all(|(a, k)| !(&dot_int(a, z) + k).is_negative())
}

/// The columns of a unimodular matrix `V` with `u·V = e1`, for `u` with no common factor: the
/// column operations of Euclid's algorithm on the entries of `u`, applied to the identity.
fn complete(u: &[Int; 3]) -> [[Int; 3]; 3] {
    let mut r = u.clone();
    let mut v: [[Int; 3]; 3] = [0, 1, 2].map(|i| [0, 1, 2].map(|j| Int::from(i64::from(i == j))));
    for j in 1..3 {
        while !r[j].is_zero() {
            let c = r[0].div_floor(&r[j]);
            r[0] = &r[0] - &(&c * &r[j]);
            let (first, rest) = v.split_at_mut(1);
            for (x, y) in first[0].iter_mut().zip(&rest[j - 1]) {
                *x = &*x - &(&c * y);
            }
            r.swap(0, j);
            v.swap(0, j);
        }
    }
    if r[0].is_negative() {
        for x in &mut v[0] {
            *x = -&*x;
        }
    }
    debug_assert!(r[0].is_unit(), "a direction with no common factor");
    v
}

/// An integer point of the rows with `u·x = t` for an integer `t` in `[lo, hi]`, which holds
/// every value of `u·x` over the real points of the rows, or `None` when no such slice has
/// one. With `x = V·(t, w1, w2)` each slice
/// is a system over `w1` and `w2`. There are fewer than 199 slices, `w(3)`, a constant of the
/// dimension that bounds the work and is never a budget: every slice is tried.
fn slices(rows: &[Row3], u: &[Int; 3], lo: &Q, hi: &Q) -> Option<[Int; 3]> {
    let v = complete(u);
    let mut t = lo.ceil();
    let top = hi.floor();
    // Each row over `(t, w1, w2)`, built once: its coefficient at `t`, its terms over `w1` and
    // `w2`, and its constant at the current `t`, which moves by the coefficient at `t` from one
    // slice to the next.
    let mut rs: Vec<(Int, Vec<Term>, Int)> = rows
        .iter()
        .map(|(a, k)| {
            let [c0, c1, c2] = [0, 1, 2].map(|j| dot_int(a, &v[j]));
            let at_t = &(&c0 * &t) + k;
            let terms = [(0, c1), (1, c2)]
                .into_iter()
                .filter(|(_, c)| !c.is_zero())
                .collect();
            (c0, terms, at_t)
        })
        .collect();
    while t <= top {
        let refs: Vec<(&[Term], &Int)> = rs.iter().map(|(_, a, k)| (a.as_slice(), k)).collect();
        if let Some((w1, w2)) = twovar::point(&refs, 0, Some(1), true) {
            return Some(
                [0, 1, 2].map(|i| &(&(&v[0][i] * &t) + &(&v[1][i] * &w1)) + &(&v[2][i] * &w2)),
            );
        }
        for (c0, _, k) in &mut rs {
            *k = &*k + &*c0;
        }
        t = &t + &Int::ONE;
    }
    None
}

/// An integer point of the rows `a·x + k >= 0` over three variables, or `None` when they have
/// none. Complete: no system is refused.
pub fn point(rows: &[Row3]) -> Option<[Int; 3]> {
    let a = rows
        .iter()
        .flat_map(|(a, _)| a.iter().map(Int::abs))
        .fold(Int::ONE, Int::max);
    let k = rows.iter().map(|(_, k)| k.abs()).fold(Int::ZERO, Int::max);
    let m = &(&Int::from(24) * &(&a * &a)) * &a.clone().max(k);
    // A side of the box that a row over one variable bounds already is left out: the row
    // implies it, since its constant is at most `K`.
    let bounded = |i: usize, s: bool| {
        rows.iter()
            .any(|(a, _)| (0..3).all(|j| (j == i) != a[j].is_zero()) && a[i].is_positive() == s)
    };
    let bx: Vec<Row3> = (0..3)
        .flat_map(|i| [true, false].map(|s| (i, s)))
        .filter(|&(i, s)| !bounded(i, s))
        .map(|(i, s)| {
            let mut a = [Int::ZERO, Int::ZERO, Int::ZERO];
            a[i] = Int::from(if s { 1 } else { -1 });
            (a, m.clone())
        })
        .collect();
    let shape = match simplex(rows, &bx) {
        Ok(s) => reduce(rows, &s),
        Err(shape) => *shape,
    };
    match shape {
        Shape::Empty => None,
        Shape::Point(z) => Some(z),
        Shape::Dir(u, lo, hi) => slices(rows, &u, &lo, &hi),
    }
}

/// [`point`] for rows of the Omega test over the variables `vs`.
pub fn decide(rows: &[(&[Term], &Int)], vs: &[usize; 3]) -> Option<[Int; 3]> {
    let rs: Vec<Row3> = rows
        .iter()
        .map(|(a, k)| {
            let mut c = [Int::ZERO, Int::ZERO, Int::ZERO];
            for (v, x) in a.iter() {
                let i = vs.iter().position(|w| w == v).expect("a live variable");
                c[i] = x.clone();
            }
            (c, (*k).clone())
        })
        .collect();
    point(&rs)
}
