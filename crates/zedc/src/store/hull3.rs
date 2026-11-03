//! The shadow of a polyhedron in three variables on its last two (DESIGN.md sec:domains, step
//! L1.38, XT3 B4): rows `cz·z + cx·x + cy·y + k >= 0` with `cz != 0`, and the pairs of a lower
//! bound on `z` (`cz > 0`) and an upper one (`cz < 0`) whose combinations, `z` cancelled, cut
//! out exactly the real projection of the rows on `(x, y)`. Fourier–Motzkin writes every pair;
//! the pairs needed are the edges where the top of the polyhedron meets its bottom, O(m) of
//! them, found here in O(m log m).
//!
//! In each plane `y = t` the lower bounds form a convex envelope `F_t(x)` and the upper bounds
//! a concave one `G_t(x)`, and the projection is the range `F_t <= G_t`. The planes are sorted
//! by the slope of their line in `x`, and split in halves recursively. At a node, the lower
//! bounds of the left half against the upper bounds of the right half (each of the first of
//! less slope) give a range `x >= x12(t)`, and the reverse pair a range `x <= x21(t)`; the
//! projection is the meet of these ranges over all nodes, since each pair of a lower and an
//! upper bound is split at exactly one node. As `t` runs from minus to plus infinity, each node
//! follows the pieces of its two envelopes (Chan's kinetic merge, "A minimalist's
//! implementation of 3-d divide-and-conquer convex hull", 2003, in the dual form of lines) and
//! the pair of planes that meet at `x12` and at `x21`; every change happens where three planes
//! meet, and the changes at a node are linear in its planes. Each node keeps the greatest of
//! the lower lines `x >= ...` of its subtree and the least of the upper ones as envelopes in the
//! `(t, x)` plane, merged in linear time, and those of the root are the answer.
//!
//! Exact arithmetic on `Int` throughout. Ties are broken symbolically: `x` is read as
//! `x'` and `y` as `t + ε·x'`, an exact change of coordinates that makes the slopes of the
//! lines in `x'` distinct, and each constant `k` of the `i`th plane is read as `k + δ_i`. The
//! infinitesimals are ordered `1 ≫ ε ≫ δ_0 ≫ ε·δ_0 ≫ δ_1 ≫ …`, so no three planes meet at
//! one time unless they share it and no four at all (simulation of simplicity). The relaxed
//! rows lose no point, and each combination is relaxed in turn, so the chosen rows read
//! without `δ` hold the projection and no point outside it.

use super::int::Int;

/// A row `z·Z + x·X + y·Y + k >= 0`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Plane {
    /// The coefficient of `Z`.
    pub z: Int,
    /// The coefficient of `X`.
    pub x: Int,
    /// The coefficient of `Y`.
    pub y: Int,
    /// The constant.
    pub k: Int,
}

/// The pairs `(lower, upper)`, by place in `planes`, whose combinations cut out the real
/// projection of `planes` on `(x, y)`: rows with a lower bound on `z` (`z > 0`) and an upper
/// one (`z < 0`), so that `-upper.z · lower + lower.z · upper` has no `z`. An empty projection
/// gives pairs whose rows have no common point, possibly a single pair of parallel planes
/// whose combination is a false constant. Every plane must have `z != 0`.
pub fn shadow(planes: &[Plane]) -> Vec<(usize, usize)> {
    let ps: Vec<P> = planes
        .iter()
        .enumerate()
        .map(|(id, p)| {
            assert!(!p.z.is_zero(), "hull3::shadow takes rows with a z term");
            P {
                z: p.z.clone(),
                x: p.x.clone(),
                y: p.y.clone(),
                k: Pert::of(&p.k, id),
            }
        })
        .collect();
    let mut order: Vec<usize> = (0..ps.len()).collect();
    order.sort_by(|&p, &q| key_cmp(&ps[p], &ps[q]).then_with(|| ps[q].lower().cmp(&ps[p].lower())));
    // Of parallel planes on one side the tightest is kept; a parallel lower and upper bound
    // whose combination is false leave nothing to project.
    let mut kept: Vec<usize> = Vec::with_capacity(order.len());
    for &q in &order {
        match kept.last_mut() {
            Some(p) if key_cmp(&ps[*p], &ps[q]).is_eq() && ps[*p].lower() == ps[q].lower() => {
                if tighter(&ps[q], &ps[*p]) {
                    *p = q;
                }
            }
            _ => kept.push(q),
        }
    }
    for w in kept.windows(2) {
        let (p, q) = (w[0], w[1]);
        if key_cmp(&ps[p], &ps[q]).is_eq() && line(&ps, p, q).ga.sign() < 0 {
            return vec![(p, q)];
        }
    }
    let n = kept.len();
    if n == 0 {
        return Vec::new();
    }
    let mut h = Hull {
        ps: kept.iter().map(|&i| ps[i].clone()).collect(),
        prev: vec![n; n + 1],
        next: vec![n; n + 1],
        nil: n,
    };
    let out = h.solve(0, n);
    out.lo
        .iter()
        .chain(&out.hi)
        .map(|l| (kept[l.lo], kept[l.hi]))
        .collect()
}

fn sg(v: &Int) -> i32 {
    if v.is_negative() {
        -1
    } else {
        i32::from(v.is_positive())
    }
}

/// `a + ε·b`.
#[derive(Clone, Debug)]
struct Lin {
    a: Int,
    b: Int,
}

impl Lin {
    fn sign(&self) -> i32 {
        match sg(&self.a) {
            0 => sg(&self.b),
            s => s,
        }
    }
}

/// A sum of integer multiples of `1`, `ε`, `δ_i` and `ε·δ_i`, the terms held by code `0`, `1`,
/// `2 + 2i` and `3 + 2i`, which is their order of size, with no zero term.
#[derive(Clone, Debug, Default)]
struct Pert(Vec<(usize, Int)>);

impl Pert {
    /// `k + δ_id`.
    fn of(k: &Int, id: usize) -> Pert {
        let mut v = Vec::with_capacity(2);
        if !k.is_zero() {
            v.push((0, k.clone()));
        }
        v.push((2 + 2 * id, Int::ONE));
        Pert(v)
    }

    fn plus(&self, o: &Pert) -> Pert {
        let (a, b) = (&self.0, &o.0);
        let mut v = Vec::with_capacity(a.len() + b.len());
        let (mut i, mut j) = (0, 0);
        while i < a.len() || j < b.len() {
            if j == b.len() || (i < a.len() && a[i].0 < b[j].0) {
                v.push(a[i].clone());
                i += 1;
            } else if i == a.len() || b[j].0 < a[i].0 {
                v.push(b[j].clone());
                j += 1;
            } else {
                let s = &a[i].1 + &b[j].1;
                if !s.is_zero() {
                    v.push((a[i].0, s));
                }
                i += 1;
                j += 1;
            }
        }
        Pert(v)
    }

    fn minus(&self, o: &Pert) -> Pert {
        self.plus(&o.times(&-&Int::ONE))
    }

    fn times(&self, c: &Int) -> Pert {
        if c.is_zero() {
            return Pert::default();
        }
        Pert(self.0.iter().map(|(t, v)| (*t, v * c)).collect())
    }

    /// The product with `l`, `self` having no term in `ε`.
    fn times_lin(&self, l: &Lin) -> Pert {
        debug_assert!(self.0.iter().all(|(t, _)| t % 2 == 0));
        let by_eps = if l.b.is_zero() {
            Pert::default()
        } else {
            Pert(self.0.iter().map(|(t, v)| (t + 1, v * &l.b)).collect())
        };
        self.times(&l.a).plus(&by_eps)
    }

    fn sign(&self) -> i32 {
        self.0.first().map_or(0, |(_, v)| sg(v))
    }
}

/// The time `n / d`, `d > 0`.
#[derive(Clone, Debug)]
struct Time {
    n: Pert,
    d: Int,
}

impl Time {
    /// `-num / den`, `den != 0`.
    fn of(num: &Pert, den: &Int) -> Time {
        if den.is_positive() {
            Time {
                n: num.times(&-&Int::ONE),
                d: den.clone(),
            }
        } else {
            Time {
                n: num.clone(),
                d: -den,
            }
        }
    }

    fn after(&self, o: &Time) -> bool {
        self.n.times(&o.d).minus(&o.n.times(&self.d)).sign() > 0
    }
}

/// A plane with its relaxed constant.
#[derive(Clone, Debug)]
struct P {
    z: Int,
    x: Int,
    y: Int,
    k: Pert,
}

impl P {
    fn lower(&self) -> bool {
        self.z.is_positive()
    }
}

/// `| p.z  p.x' |`
/// `| q.z  q.x' |`, with `x' = x + ε·y`.
fn det2(p: &P, q: &P) -> Lin {
    Lin {
        a: &(&p.z * &q.x) - &(&q.z * &p.x),
        b: &(&p.z * &q.y) - &(&q.z * &p.y),
    }
}

/// The order of the slopes `-x'/z` of two planes' lines in `x'`.
fn key_cmp(p: &P, q: &P) -> std::cmp::Ordering {
    (det2(p, q).sign() * sg(&p.z) * sg(&q.z)).cmp(&0)
}

/// Whether `p` bounds `z` more tightly than its parallel `q` on the same side: the lesser
/// `k / |z|`.
fn tighter(p: &P, q: &P) -> bool {
    p.k.times(&q.z.abs()).minus(&q.k.times(&p.z.abs())).sign() < 0
}

/// The combination of the lower bound `i` and the upper bound `j`: the row
/// `α·x + β·y + γ >= 0`, held as `A = α + ε·β`, which is `A·x' + β·t + γ >= 0`.
#[derive(Clone, Debug)]
struct Line {
    lo: usize,
    hi: usize,
    a: Lin,
    ga: Pert,
}

fn line(ps: &[P], i: usize, j: usize) -> Line {
    let (p, q) = (&ps[i], &ps[j]);
    let (mi, mj) = (-&q.z, p.z.clone());
    Line {
        lo: i,
        hi: j,
        a: Lin {
            a: &(&mi * &p.x) + &(&mj * &q.x),
            b: &(&mi * &p.y) + &(&mj * &q.y),
        },
        ga: p.k.times(&mi).plus(&q.k.times(&mj)),
    }
}

/// For the bounds `x'_1(t)` and `x'_2(t)` of two lines: `c` with the sign of their slopes'
/// difference over `s`, and `P`, so that `x'_1 - x'_2` has the sign of `s·(c·t + P)`.
fn compare(l1: &Line, l2: &Line) -> (Int, Pert, i32) {
    let c = &(&l1.a.a * &l2.a.b) - &(&l2.a.a * &l1.a.b);
    let p = l2.ga.times_lin(&l1.a).minus(&l1.ga.times_lin(&l2.a));
    (c, p, l1.a.sign() * l2.a.sign())
}

/// The sign of `x'_1(t) - x'_2(t)`.
fn diff_at(l1: &Line, l2: &Line, t: &Time) -> i32 {
    let (c, p, s) = compare(l1, l2);
    s * p.times(&t.d).plus(&t.n.times(&c)).sign()
}

/// The greatest (`up`) or least of lines whose bounds are each sorted by rising slope (`up`)
/// or falling, as the pieces of their envelope in the order of `t`.
fn envelope(lists: [Vec<Line>; 3], up: bool) -> Vec<Line> {
    let s: i32 = if up { 1 } else { -1 };
    // Whether the slope of `a` comes before that of `b` in the envelope's order.
    let before = |a: &Line, b: &Line| {
        let (c, _, sa) = compare(a, b);
        s * sa * sg(&c) < 0
    };
    let [a, b, c] = lists;
    let mut merged: Vec<Line> = Vec::with_capacity(a.len() + b.len() + c.len());
    let mut ab: Vec<Line> = Vec::with_capacity(a.len() + b.len());
    merge_by(a, b, &mut ab, &before);
    merge_by(ab, c, &mut merged, &before);
    let mut st: Vec<Line> = Vec::with_capacity(merged.len());
    for l in merged {
        if let Some(top) = st.last() {
            let (c, p, sa) = compare(&l, top);
            if c.is_zero() {
                if s * sa * p.sign() <= 0 {
                    continue;
                }
                st.pop();
            }
        }
        while st.len() >= 2 {
            let (a, b) = (&st[st.len() - 2], &st[st.len() - 1]);
            let (c, p, _) = compare(a, b);
            let t = Time::of(&p, &c);
            if s * diff_at(&l, b, &t) >= 0 {
                st.pop();
            } else {
                break;
            }
        }
        st.push(l);
    }
    st
}

fn merge_by(
    a: Vec<Line>,
    b: Vec<Line>,
    into: &mut Vec<Line>,
    before: &impl Fn(&Line, &Line) -> bool,
) {
    let mut b = b.into_iter().peekable();
    for x in a {
        while let Some(y) = b.next_if(|y| before(y, &x)) {
            into.push(y);
        }
        into.push(x);
    }
    into.extend(b);
}

/// What a node gives its parent: the events of its two envelopes in the order of time, each
/// the plane put in or taken out of the list at that time, the lower and upper lines of its
/// projection, and the ends of its envelopes (`nil` when it has none).
struct Out {
    f: Vec<usize>,
    g: Vec<usize>,
    lo: Vec<Line>,
    hi: Vec<Line>,
    /// The first and last lower bound by slope, the ends of the envelope of lower bounds.
    f_first: usize,
    f_last: usize,
    /// The first and last upper bound by slope, the right and left ends of the envelope of
    /// upper bounds.
    g_first: usize,
    g_last: usize,
}

/// The merge of the envelopes of two halves on one side, as in Chan's code: `a` the half on
/// the left in `x'`, `b` the other, their events, and the bridge `u`–`v` between them.
struct Merge {
    a: Vec<usize>,
    b: Vec<usize>,
    ia: usize,
    ib: usize,
    u: usize,
    v: usize,
    /// Whether both halves have planes on this side; otherwise the events of one pass.
    both: bool,
    /// Whether the order in `x'` is that of falling slope (upper bounds).
    rev: bool,
    /// The first place of the right half by slope.
    mid: usize,
    out: Vec<usize>,
}

impl Merge {
    fn left_of(&self, p: usize, q: usize) -> bool {
        if self.rev { p > q } else { p < q }
    }

    fn in_a(&self, q: usize) -> bool {
        (q < self.mid) != self.rev
    }
}

/// The pair of a lower bound `i` and an upper bound `j` whose lines in `x'` meet where the
/// lower envelope of one half crosses the upper envelope of the other, with the lines of the
/// pairs it has held.
struct Chain {
    on: bool,
    i: usize,
    j: usize,
    pieces: Vec<Line>,
}

#[derive(Clone, Copy)]
enum Ev {
    /// The next event of half `a` (`false`) or `b` of merge `m`.
    Child(usize, bool),
    /// A change of the bridge of merge `m`, as numbered in Chan's code (2 to 5).
    Bridge(usize, u8),
    /// A step of chain `c`: `i` back or on, `j` back or on.
    Step(usize, u8),
}

struct Hull {
    ps: Vec<P>,
    prev: Vec<usize>,
    next: Vec<usize>,
    nil: usize,
}

impl Hull {
    /// The time when the planes meet in a point, if they ever do.
    fn when(&self, p: usize, q: usize, r: usize) -> Option<Time> {
        if p == self.nil || q == self.nil || r == self.nil {
            return None;
        }
        let (p, q, r) = (&self.ps[p], &self.ps[q], &self.ps[r]);
        let dt = det3(p, q, r);
        if dt.is_zero() {
            return None;
        }
        Some(Time::of(&dc(p, q, r), &dt))
    }

    /// Whether, as `t` tends to minus infinity, plane `r` is false where `p` and `q` meet.
    fn violated(&self, p: usize, q: usize, r: usize) -> bool {
        let (p, q, r) = (&self.ps[p], &self.ps[q], &self.ps[r]);
        let dt = det3(p, q, r);
        let m = if dt.is_zero() {
            dc(p, q, r).sign()
        } else {
            -sg(&dt)
        };
        m * det2(p, q).sign() < 0
    }

    /// Whether `q` lies off its envelope between `p` and `r` as `t` tends to minus infinity.
    fn hidden(&self, p: usize, q: usize, r: usize) -> bool {
        p != self.nil && q != self.nil && r != self.nil && !self.violated(p, r, q)
    }

    /// Puts `q` into its list between its neighbors, or takes it out.
    fn act(&mut self, q: usize) {
        let (p, r) = (self.prev[q], self.next[q]);
        if self.next[p] != q {
            self.next[p] = q;
            self.prev[r] = q;
        } else {
            self.next[p] = r;
            self.prev[r] = p;
        }
    }

    // The recursion is as deep as the logarithm of the number of planes.
    fn solve(&mut self, a: usize, b: usize) -> Out {
        let nil = self.nil;
        if b - a == 1 {
            self.prev[a] = nil;
            self.next[a] = nil;
            let (f, g) = if self.ps[a].lower() {
                (a, nil)
            } else {
                (nil, a)
            };
            return Out {
                f: Vec::new(),
                g: Vec::new(),
                lo: Vec::new(),
                hi: Vec::new(),
                f_first: f,
                f_last: f,
                g_first: g,
                g_last: g,
            };
        }
        let mid = a + (b - a) / 2;
        let l = self.solve(a, mid);
        let r = self.solve(mid, b);
        let either = |x: usize, y: usize| if x == nil { y } else { x };
        let mut cs = [self.chain12(&l, &r), self.chain21(&l, &r)];
        let mut ms = [
            self.merge(l.f, r.f, l.f_last, r.f_first, false, mid),
            self.merge(r.g, l.g, r.g_first, l.g_last, true, mid),
        ];
        let mut last: Option<Time> = None;
        loop {
            let mut best: Option<(Time, Ev)> = None;
            let mut offer = |t: Option<Time>, e: Ev| {
                if let Some(t) = t
                    && last.as_ref().is_none_or(|l| t.after(l))
                    && best.as_ref().is_none_or(|(b, _)| b.after(&t))
                {
                    best = Some((t, e));
                }
            };
            for (k, m) in ms.iter().enumerate() {
                if let Some(&q) = m.a.get(m.ia) {
                    offer(
                        self.when(self.prev[q], q, self.next[q]),
                        Ev::Child(k, false),
                    );
                }
                if let Some(&q) = m.b.get(m.ib) {
                    offer(self.when(self.prev[q], q, self.next[q]), Ev::Child(k, true));
                }
                if m.both {
                    let (u, v) = (m.u, m.v);
                    offer(self.when(u, self.next[u], v), Ev::Bridge(k, 2));
                    offer(self.when(self.prev[u], u, v), Ev::Bridge(k, 3));
                    offer(self.when(u, self.prev[v], v), Ev::Bridge(k, 4));
                    offer(self.when(u, v, self.next[v]), Ev::Bridge(k, 5));
                }
            }
            for (k, c) in cs.iter().enumerate() {
                if c.on {
                    let (i, j) = (c.i, c.j);
                    offer(self.when(self.prev[i], i, j), Ev::Step(k, 0));
                    offer(self.when(i, self.next[i], j), Ev::Step(k, 1));
                    offer(self.when(self.prev[j], j, i), Ev::Step(k, 2));
                    offer(self.when(j, self.next[j], i), Ev::Step(k, 3));
                }
            }
            let Some((t, e)) = best else { break };
            last = Some(t);
            match e {
                Ev::Child(k, in_b) => {
                    let m = &mut ms[k];
                    let q = if in_b {
                        m.ib += 1;
                        m.b[m.ib - 1]
                    } else {
                        m.ia += 1;
                        m.a[m.ia - 1]
                    };
                    let shown = !m.both
                        || if in_b {
                            m.left_of(m.v, q)
                        } else {
                            m.left_of(q, m.u)
                        };
                    if shown {
                        m.out.push(q);
                    }
                    self.act(q);
                }
                Ev::Bridge(k, w) => {
                    let m = &mut ms[k];
                    match w {
                        2 => {
                            m.u = self.next[m.u];
                            m.out.push(m.u);
                        }
                        3 => {
                            m.out.push(m.u);
                            m.u = self.prev[m.u];
                        }
                        4 => {
                            m.v = self.prev[m.v];
                            m.out.push(m.v);
                        }
                        _ => {
                            m.out.push(m.v);
                            m.v = self.next[m.v];
                        }
                    }
                }
                Ev::Step(k, w) => {
                    let c = &mut cs[k];
                    match w {
                        0 => c.i = self.prev[c.i],
                        1 => c.i = self.next[c.i],
                        2 => c.j = self.prev[c.j],
                        _ => c.j = self.next[c.j],
                    }
                    c.pieces.push(line(&self.ps, c.i, c.j));
                }
            }
        }
        let [mf, mg] = ms;
        let f = self.unwind(mf);
        let g = self.unwind(mg);
        let [c12, c21] = cs;
        Out {
            f,
            g,
            lo: envelope([l.lo, r.lo, c12.pieces], true),
            hi: envelope([l.hi, r.hi, c21.pieces], false),
            f_first: either(l.f_first, r.f_first),
            f_last: either(r.f_last, l.f_last),
            g_first: either(l.g_first, r.g_first),
            g_last: either(r.g_last, l.g_last),
        }
    }

    /// The merge of the halves' envelopes on one side, with the bridge found as `t` tends to
    /// minus infinity: `ua` the right end of half `a`, `vb` the left end of half `b`.
    fn merge(
        &self,
        a: Vec<usize>,
        b: Vec<usize>,
        ua: usize,
        vb: usize,
        rev: bool,
        mid: usize,
    ) -> Merge {
        let nil = self.nil;
        let both = ua != nil && vb != nil;
        let (mut u, mut v) = (ua, vb);
        if both {
            loop {
                if self.hidden(u, v, self.next[v]) {
                    v = self.next[v];
                } else if self.hidden(self.prev[u], u, v) {
                    u = self.prev[u];
                } else {
                    break;
                }
            }
        }
        Merge {
            a,
            b,
            ia: 0,
            ib: 0,
            u,
            v,
            both,
            rev,
            mid,
            out: Vec::new(),
        }
    }

    /// The pair where the lower envelope of the left half, of lesser slopes, crosses the upper
    /// envelope of the right half, as `t` tends to minus infinity: the bound `x' >= x12(t)`,
    /// found from the left.
    fn chain12(&self, l: &Out, r: &Out) -> Chain {
        let nil = self.nil;
        let (mut i, mut j) = (l.f_first, r.g_last);
        // A single lower and a single upper bound, parallel, bound nothing: the planes were
        // checked to have a point.
        let on = i != nil
            && j != nil
            && !(i == l.f_last && j == r.g_first && key_cmp(&self.ps[i], &self.ps[j]).is_eq());
        if !on {
            return Chain {
                on,
                i,
                j,
                pieces: Vec::new(),
            };
        }
        loop {
            if self.next[i] != nil && self.violated(i, self.next[i], j) {
                i = self.next[i];
            } else if self.next[j] != nil && self.violated(j, self.next[j], i) {
                j = self.next[j];
            } else {
                break;
            }
        }
        Chain {
            on,
            i,
            j,
            pieces: vec![line(&self.ps, i, j)],
        }
    }

    /// The pair where the lower envelope of the right half crosses the upper envelope of the
    /// left half: the bound `x' <= x21(t)`, found from the right.
    fn chain21(&self, l: &Out, r: &Out) -> Chain {
        let nil = self.nil;
        let (mut i, mut j) = (r.f_last, l.g_first);
        let on = i != nil && j != nil;
        if !on {
            return Chain {
                on,
                i,
                j,
                pieces: Vec::new(),
            };
        }
        loop {
            if self.prev[i] != nil && self.violated(self.prev[i], i, j) {
                i = self.prev[i];
            } else if self.prev[j] != nil && self.violated(self.prev[j], j, i) {
                j = self.prev[j];
            } else {
                break;
            }
        }
        Chain {
            on,
            i,
            j,
            pieces: vec![line(&self.ps, i, j)],
        }
    }

    /// Runs time back to minus infinity, leaving the merged list as it is then, and returns
    /// the merged events.
    fn unwind(&mut self, m: Merge) -> Vec<usize> {
        if !m.both {
            for &q in m.out.iter().rev() {
                self.act(q);
            }
            return m.out;
        }
        let (mut u, mut v) = (m.u, m.v);
        self.next[u] = v;
        self.prev[v] = u;
        for &q in m.out.iter().rev() {
            if !(m.left_of(u, q) && m.left_of(q, v)) {
                self.act(q);
                if q == u {
                    u = self.prev[u];
                } else if q == v {
                    v = self.next[v];
                }
            } else {
                self.next[u] = q;
                self.prev[q] = u;
                self.prev[v] = q;
                self.next[q] = v;
                if m.in_a(q) {
                    u = q;
                } else {
                    v = q;
                }
            }
        }
        m.out
    }
}

/// `det [p; q; r]` of the columns `z`, `x`, `y`, the same in `x'`.
fn det3(p: &P, q: &P, r: &P) -> Int {
    let m = |a: &Int, b: &Int, c: &Int, d: &Int| &(a * d) - &(b * c);
    &(&(&p.z * &m(&q.x, &q.y, &r.x, &r.y)) - &(&p.x * &m(&q.z, &q.y, &r.z, &r.y)))
        + &(&p.y * &m(&q.z, &q.x, &r.z, &r.x))
}

/// `det [p; q; r]` of the columns `z`, `x'`, `k`.
fn dc(p: &P, q: &P, r: &P) -> Pert {
    p.k.times_lin(&det2(q, r))
        .minus(&q.k.times_lin(&det2(p, r)))
        .plus(&r.k.times_lin(&det2(p, q)))
}
