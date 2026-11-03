//! A potential of a graph with integer edge weights of any sign, or the report that it has a
//! negative cycle, by the deterministic negative-weight shortest-path algorithm of Duong [D]:
//! Goldberg's scaling, and in each scaling step a recursion that covers the vertices by padded
//! balls, solves each ball, and merges the balls' potentials by an ordered merge that runs
//! Dijkstra's search with Bellman–Ford rounds (BF-Dijkstra) on an auxiliary graph.
//!
//! The paper's decomposition has two branches; the second (peeling and residual covers) needs
//! `L >= 256` for `L = ⌈log₂ M₀⌉` and the total mass `M₀ ≈ 2m + n log log n`, so `M₀ >= 2^256`,
//! and below that the paper applies its local decomposition directly ([D] l.809, l.831). Only
//! that branch is built: it is the paper's algorithm for every graph that fits in memory.
//! Every real number of the paper is replaced by exact integers (radii by cross-multiplying
//! with `d`, a power of two), Thorup's integer queue by a binary heap, and every choice is the
//! first in vertex order, so the result depends only on the graph. COMPLEXITY.md C24 gives the
//! bound and the measurements.
//!
//! The work is done in units, a heap pop or an edge examined, and the caller's `tick` is called
//! once per unit; an error from it ends the search with that error. `utvpi` uses this to run
//! Goldberg and Radzik's search and BF-Dijkstra ([`Rounds`]) one unit each after each unit of
//! this one.
//!
//! [D]: T. Duong, "Deterministic negative-weight single-source shortest paths in near-linear
//! time", arXiv 2609.05590 (2026).

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::convert::Infallible;
use std::marker::PhantomData;
use std::ops::Range;

use super::int::Int;

const NONE: usize = usize::MAX;

/// Why a search ended before its result: the caller's tick, or a negative cycle.
enum Stop<H> {
    Tick(H),
    Negative,
}

type Step<T, H> = Result<T, Stop<H>>;

/// One unit of work.
fn unit<H>(tick: &mut impl FnMut() -> Result<(), H>) -> Step<(), H> {
    tick().map_err(Stop::Tick)
}

/// A potential of the graph `out`, its edges `u → (v, w)`: integers `p` with
/// `p(v) <= p(u) + w` on every edge, or `None` when the graph has a negative cycle. `tick` is
/// called once per unit of work; its first error is returned.
pub fn potential<H>(
    out: &[Vec<(usize, Int)>],
    tick: impl FnMut() -> Result<(), H>,
) -> Result<Option<Vec<Int>>, H> {
    let graph = Graph::new(out);
    let mut solver = Solver::new(&graph, tick);
    match solver.run() {
        Ok(p) => Ok(Some(p)),
        Err(Stop::Negative) => Ok(None),
        Err(Stop::Tick(h)) => Err(h),
    }
}

/// [`potential`] run to its end.
pub fn potential_alone(out: &[Vec<(usize, Int)>]) -> Option<Vec<Int>> {
    match potential(out, || Ok::<(), Infallible>(())) {
        Ok(found) => found,
        Err(never) => match never {},
    }
}

/// The graph in compressed rows: edge `e` is `from[e] → to[e]` of weight `w[e]`, the edges out
/// of `u` are `start[u]..start[u + 1]`, and those into `v` are listed in
/// `redge[rstart[v]..rstart[v + 1]]`.
struct Graph {
    from: Vec<usize>,
    to: Vec<usize>,
    w: Vec<Int>,
    start: Vec<usize>,
    rstart: Vec<usize>,
    redge: Vec<usize>,
    /// The mass of each vertex, its edges in and out plus `λ` ([D] eq. mass, l.139).
    mass: Vec<u64>,
}

/// `⌈log₂ x⌉`, 0 for `x <= 1`.
fn ceil_log2(x: u64) -> u64 {
    if x <= 1 {
        0
    } else {
        u64::from((x - 1).ilog2()) + 1
    }
}

impl Graph {
    fn new(out: &[Vec<(usize, Int)>]) -> Graph {
        let n = out.len();
        let m: usize = out.iter().map(Vec::len).sum();
        let (mut from, mut to, mut w) = (
            Vec::with_capacity(m),
            Vec::with_capacity(m),
            Vec::with_capacity(m),
        );
        let mut start = Vec::with_capacity(n + 1);
        start.push(0);
        for (u, edges) in out.iter().enumerate() {
            for (v, weight) in edges {
                from.push(u);
                to.push(*v);
                w.push(weight.clone());
            }
            start.push(to.len());
        }
        let mut rstart = vec![0usize; n + 1];
        for &v in &to {
            rstart[v + 1] += 1;
        }
        for v in 0..n {
            rstart[v + 1] += rstart[v];
        }
        let mut fill = rstart[..n].to_vec();
        let mut redge = vec![0usize; m];
        for (e, &v) in to.iter().enumerate() {
            redge[fill[v]] = e;
            fill[v] += 1;
        }
        // λ = ⌈log log n⌉, at least 1 so that every vertex has mass at least 1.
        let lambda = ceil_log2(ceil_log2(n as u64)).max(1);
        let mass = (0..n)
            .map(|v| (start[v + 1] - start[v] + rstart[v + 1] - rstart[v]) as u64 + lambda)
            .collect();
        Graph {
            from,
            to,
            w,
            start,
            rstart,
            redge,
            mass,
        }
    }

    fn out(&self, u: usize) -> Range<usize> {
        self.start[u]..self.start[u + 1]
    }

    fn ins(&self, v: usize) -> &[usize] {
        &self.redge[self.rstart[v]..self.rstart[v + 1]]
    }
}

/// The least power of two at or above `x`, for `x >= 1`.
fn power_of_two_at_least(x: &Int) -> Int {
    let mut p = Int::ONE;
    while p < *x {
        p = &p + &p;
    }
    p
}

/// `⌈a / b⌉` for `a >= 0` and `b > 0`.
fn ceil_div(a: &Int, b: &Int) -> Int {
    (&(a + b) - &Int::ONE).div_floor(b)
}

/// A Dijkstra search on the clipped weights `ell` within a set of vertices, along the edges
/// (`forward`) or against them, with lazy initialization: `seen` and `done` hold the epoch in
/// which a vertex was labeled and settled. A vertex is settled one edge per call of
/// [`Search::relax_one`], so that two searches can take turns by elementary operations.
struct Search {
    forward: bool,
    dist: Vec<Int>,
    seen: Vec<u64>,
    done: Vec<u64>,
    epoch: u64,
    heap: BinaryHeap<Reverse<(Int, usize)>>,
    /// The vertex being settled, its distance and the place of its next edge.
    settling: Option<(usize, Int, usize)>,
    /// The elementary operations done since the start: entries looked at and edges relaxed.
    work: u64,
}

impl Search {
    fn new(n: usize, forward: bool) -> Search {
        Search {
            forward,
            dist: vec![Int::ZERO; n],
            seen: vec![0; n],
            done: vec![0; n],
            epoch: 0,
            heap: BinaryHeap::new(),
            settling: None,
            work: 0,
        }
    }

    fn start(&mut self, epoch: u64, s: usize) {
        self.epoch = epoch;
        self.heap.clear();
        self.settling = None;
        self.work = 0;
        self.dist[s] = Int::ZERO;
        self.seen[s] = epoch;
        self.heap.push(Reverse((Int::ZERO, s)));
    }

    /// The next vertex in order of distance and its distance, not yet settled; `None` when the
    /// search has reached all it can.
    fn peek<H>(
        &mut self,
        tick: &mut impl FnMut() -> Result<(), H>,
    ) -> Step<Option<(usize, Int)>, H> {
        // The least entry of a vertex not yet settled holds its distance: an entry is pushed at
        // each fall, and the earlier ones are larger.
        while let Some(Reverse((x, v))) = self.heap.peek() {
            unit(tick)?;
            self.work += 1;
            if self.done[*v] != self.epoch {
                return Ok(Some((*v, x.clone())));
            }
            self.heap.pop();
        }
        Ok(None)
    }

    /// Starts settling the vertex `v` that [`Search::peek`] gave, at its distance `x`. A vertex
    /// is settled only when a ball takes it, so that the ball's mass pays for its edges.
    fn begin(&mut self, (v, x): (usize, Int)) {
        self.heap.pop();
        self.done[v] = self.epoch;
        self.settling = Some((v, x, 0));
    }

    /// Relaxes the next edge of the vertex being settled, to a vertex `allow` admits.
    fn relax_one<H>(
        &mut self,
        g: &Graph,
        ell: &[Int],
        allow: impl Fn(usize) -> bool,
        tick: &mut impl FnMut() -> Result<(), H>,
    ) -> Step<(), H> {
        let Some((v, x, place)) = &mut self.settling else {
            return Ok(());
        };
        let (e, y) = if self.forward {
            let e = g.start[*v] + *place;
            if e == g.start[*v + 1] {
                self.settling = None;
                return Ok(());
            }
            (e, g.to[e])
        } else {
            let Some(&e) = g.ins(*v).get(*place) else {
                self.settling = None;
                return Ok(());
            };
            (e, g.from[e])
        };
        *place += 1;
        unit(tick)?;
        self.work += 1;
        if !allow(y) || self.done[y] == self.epoch {
            return Ok(());
        }
        let to = &*x + &ell[e];
        if self.seen[y] != self.epoch || to < self.dist[y] {
            self.seen[y] = self.epoch;
            self.dist[y] = to.clone();
            self.heap.push(Reverse((to, y)));
        }
        Ok(())
    }

    /// Settles the vertex `v` that [`Search::peek`] gave, at its distance `x`, at once.
    fn settle<H>(
        &mut self,
        g: &Graph,
        ell: &[Int],
        next: (usize, Int),
        allow: impl Fn(usize) -> bool,
        tick: &mut impl FnMut() -> Result<(), H>,
    ) -> Step<(), H> {
        self.begin(next);
        while self.settling.is_some() {
            self.relax_one(g, ell, &allow, tick)?;
        }
        Ok(())
    }
}

/// The constants of one decomposition: the mass `m` of the set, `L`, and the radius step
/// `d / scale`.
struct Radii<'a> {
    m: u64,
    l: u64,
    scale: &'a Int,
    d: &'a Int,
}

/// What a ball did with the next vertex of its search.
enum Fed {
    /// Took it into its core or shell, so the search settles it.
    Took,
    /// Left it: the core has mass at least `m / 8`.
    Heavy,
    /// Left it: the core is light, and the pad's shell passes the test of [D] eq.
    /// adaptive-shell.
    Light,
}

/// A ball grown in steps of the radius `δ₀` ([D] Lemma 4.4): `core` is the ball of radius
/// `t·δ₀` once `closed`, and `shell` the vertices up to `(t + 1)·δ₀` met so far.
#[derive(Default)]
struct Ball {
    t: Int,
    core: Vec<usize>,
    core_mass: u64,
    shell: Vec<usize>,
    shell_mass: u64,
    closed: bool,
    heavy: bool,
}

impl Ball {
    /// Offers the next vertex of the search and its distance, or `None` at its end.
    fn feed(&mut self, next: Option<(usize, &Int)>, mass: &[u64], at: &Radii) -> Fed {
        // The least `t` with the vertex in the ball of radius `t·δ₀`.
        let next = next.map(|(v, x)| (v, ceil_div(&(x * at.scale), at.d)));
        if !self.closed {
            if let Some((v, i)) = &next
                && *i <= self.t
            {
                self.core.push(*v);
                self.core_mass += mass[*v];
                return Fed::Took;
            }
            self.closed = true;
            if 8 * self.core_mass >= at.m {
                self.heavy = true;
                return Fed::Heavy;
            }
        }
        loop {
            let t1 = &self.t + &Int::ONE;
            if let Some((v, i)) = &next
                && *i == t1
            {
                self.shell.push(*v);
                self.shell_mass += mass[*v];
                return Fed::Took;
            }
            // The shell is complete. The core is light, so `m / core_mass >= 8`.
            let log = u128::from((at.m / self.core_mass).ilog2());
            if 24 * u128::from(at.l) * u128::from(self.shell_mass)
                <= u128::from(self.core_mass) * log
            {
                return Fed::Light;
            }
            self.core.append(&mut self.shell);
            self.core_mass += self.shell_mass;
            self.shell_mass = 0;
            self.t = t1;
            if 8 * self.core_mass >= at.m {
                self.heavy = true;
                return Fed::Heavy;
            }
        }
    }
}

/// The children of a decomposition, each with whether its distance scale is halved.
type Cover = Vec<(Vec<usize>, bool)>;

struct Solver<'g, H, F> {
    g: &'g Graph,
    tick: F,
    /// This scaling step's weights shifted by `W / 2`, and clipped at 0 ([D] eq. scale).
    c: Vec<Int>,
    ell: Vec<Int>,
    /// This scaling step's `W`.
    big_w: Int,
    l: u64,
    /// `32·N₀` and `32·N_h`, so that `δ₀ = d / scale0` and `δ_h = d / scale_h`; `N_h`.
    scale0: Int,
    scale_h: Int,
    n_h: u64,
    /// The rounds after which a merge's BF-Dijkstra shows a negative cycle, `32·N₀ + 3`.
    eta: u64,
    /// The last id given to a set; sets are marked by stamps.
    ids: u64,
    member: Vec<u64>,
    plus: Vec<u64>,
    minus: Vec<u64>,
    /// The place of each vertex in the set being merged.
    local: Vec<usize>,
    outward: Search,
    inward: Search,
    stop: PhantomData<fn() -> H>,
}

impl<'g, H, F: FnMut() -> Result<(), H>> Solver<'g, H, F> {
    fn new(g: &'g Graph, tick: F) -> Self {
        let n = g.mass.len();
        let m0: u64 = g.mass.iter().sum();
        let l = ceil_log2(m0).max(1);
        // N₀ = ⌈16 L ⌈log L⌉ / θ⌉ and N_h = ⌈16 L / θ⌉ with θ = 1/24 ([D] eq. micro-width).
        let n0 = 384 * l * ceil_log2(l).max(1);
        let n_h = 384 * l;
        Solver {
            g,
            tick,
            c: Vec::new(),
            ell: Vec::new(),
            big_w: Int::ONE,
            l,
            scale0: Int::from(i128::from(32 * n0)),
            scale_h: Int::from(i128::from(32 * n_h)),
            n_h,
            eta: 32 * n0 + 3,
            ids: 0,
            member: vec![0; n],
            plus: vec![0; n],
            minus: vec![0; n],
            local: vec![0; n],
            outward: Search::new(n, true),
            inward: Search::new(n, false),
            stop: PhantomData,
        }
    }

    fn next_id(&mut self) -> u64 {
        self.ids += 1;
        self.ids
    }

    /// Marks the set `x` as the current one and returns its id.
    fn stamp(&mut self, x: &[usize]) -> u64 {
        let id = self.next_id();
        for &v in x {
            self.member[v] = id;
        }
        id
    }

    /// Goldberg's scaling ([D] Lemma 2.1) on the weights times `n + 1`, then one Dijkstra
    /// search that reads off exact distances (design review, section 3.2).
    fn run(&mut self) -> Step<Vec<Int>, H> {
        let g = self.g;
        let (n, m) = (g.mass.len(), g.to.len());
        let k = Int::from(n + 1);
        let scaled: Vec<Int> = g.w.iter().map(|w| w * &k).collect();
        let mut phi = vec![Int::ZERO; n];
        let mut r = vec![Int::ZERO; m];
        let two = Int::from(2);
        loop {
            let mut low = Int::ZERO;
            for e in 0..m {
                unit(&mut self.tick)?;
                r[e] = &(&scaled[e] + &phi[g.from[e]]) - &phi[g.to[e]];
                if r[e] < low {
                    low = r[e].clone();
                }
            }
            let need = -&low;
            if need <= Int::ONE {
                break;
            }
            // A step: a potential valid for `c = r + W/2` leaves every reduced weight at least
            // `-W/2`.
            self.big_w = power_of_two_at_least(&need);
            let half = self.big_w.div_floor(&two);
            self.c = r.iter().map(|x| x + &half).collect();
            self.ell = self
                .c
                .iter()
                .map(|x| {
                    if x.is_negative() {
                        Int::ZERO
                    } else {
                        x.clone()
                    }
                })
                .collect();
            let d0 = power_of_two_at_least(&(&Int::from(n) * &self.big_w));
            let all: Vec<usize> = (0..n).collect();
            let psi = self.solve(&all, d0)?;
            for (p, q) in phi.iter_mut().zip(&psi) {
                *p = &*p + q;
            }
        }
        // Every reduced weight is at least -1. Dijkstra on `r + 1`, each vertex starting at
        // `-phi`, labels a path `P` to `v` with `(n + 1)·w(P) + |P| - phi(v)`, so its tree paths
        // are shortest in `w`; their weights in `w` are the potential.
        let mut label: Vec<Int> = phi.iter().map(|p| -p).collect();
        let mut via = vec![NONE; n];
        let mut settled = vec![false; n];
        let mut found = vec![Int::ZERO; n];
        let mut heap: BinaryHeap<Reverse<(Int, usize)>> =
            label.iter().cloned().zip(0..).map(Reverse).collect();
        while let Some(Reverse((x, v))) = heap.pop() {
            unit(&mut self.tick)?;
            if settled[v] || x != label[v] {
                continue;
            }
            settled[v] = true;
            if via[v] != NONE {
                let e = via[v];
                found[v] = &found[g.from[e]] + &g.w[e];
            }
            for e in g.out(v) {
                unit(&mut self.tick)?;
                let y = g.to[e];
                if settled[y] {
                    continue;
                }
                let to = &(&x + &r[e]) + &Int::ONE;
                if to < label[y] {
                    label[y] = to.clone();
                    via[y] = e;
                    heap.push(Reverse((to, y)));
                }
            }
        }
        Ok(found)
    }

    /// A potential valid for `c` on `G[x]`, in the order of `x` ([D] Algorithm 3). The depth of
    /// the recursion is at most `log_{8/7} M₀ + log₂(d₀ / W) + 2`: each child has at most 7/8
    /// of its parent's mass or half its `d`.
    fn solve(&mut self, x: &[usize], d: Int) -> Step<Vec<Int>, H> {
        let g = self.g;
        let id = self.stamp(x);
        let mut negative = false;
        'scan: for &u in x {
            for e in g.out(u) {
                unit(&mut self.tick)?;
                if self.member[g.to[e]] == id && self.c[e].is_negative() {
                    negative = true;
                    break 'scan;
                }
            }
        }
        if !negative {
            return Ok(vec![Int::ZERO; x.len()]);
        }
        // `d < W/2`: `x` has weak diameter at most `d`, so the edge closes a negative cycle
        // ([D] l.889).
        if &d + &d < self.big_w {
            return Err(Stop::Negative);
        }
        let children = self.decompose(x, id, &d)?;
        let half = d.div_floor(&Int::from(2));
        let mut solved = Vec::with_capacity(children.len());
        for (y, halved) in children {
            let p = self.solve(&y, if halved { half.clone() } else { d.clone() })?;
            solved.push((y, p));
        }
        self.merge(x, &solved)
    }

    /// The local decomposition of `x`, marked with `id` ([D] Lemma 4.4).
    fn decompose(&mut self, x: &[usize], id: u64, d: &Int) -> Step<Cover, H> {
        let g = self.g;
        let m: u64 = x.iter().map(|&v| g.mass[v]).sum();
        let pid = self.next_id();
        let (mut mass_plus, mut mass_minus) = (0u64, 0u64);
        let (mut pads_plus, mut pads_minus): (Vec<Vec<usize>>, Vec<Vec<usize>>) =
            (Vec::new(), Vec::new());
        let mut cursor = 0;
        while 4 * mass_plus < m && 4 * mass_minus < m {
            // The unions hold less than half the mass, so a vertex lies outside both.
            while self.plus[x[cursor]] == pid || self.minus[x[cursor]] == pid {
                cursor += 1;
            }
            let s = x[cursor];
            let epoch = self.next_id();
            self.outward.start(epoch, s);
            self.inward.start(epoch, s);
            let mut balls = [Ball::default(), Ball::default()];
            let side = loop {
                let side = match (balls[0].heavy, balls[1].heavy) {
                    (true, true) => return self.heavy(x, id, s, d),
                    (false, true) => 0,
                    (true, false) => 1,
                    // The searches take turns by elementary operations, so the one discarded
                    // has done at most one more than the one accepted ([D] l.474).
                    (false, false) => usize::from(self.outward.work > self.inward.work),
                };
                let Solver {
                    ell,
                    member,
                    plus,
                    minus,
                    outward,
                    inward,
                    tick,
                    l,
                    scale0,
                    ..
                } = self;
                let (search, union) = if side == 0 {
                    (outward, &*plus)
                } else {
                    (inward, &*minus)
                };
                let allow = |v| member[v] == id && union[v] != pid;
                if search.settling.is_some() {
                    search.relax_one(g, ell, allow, tick)?;
                    continue;
                }
                let next = search.peek(tick)?;
                let at = Radii {
                    m,
                    l: *l,
                    scale: scale0,
                    d,
                };
                match balls[side].feed(next.as_ref().map(|(v, x)| (*v, x)), &g.mass, &at) {
                    Fed::Took => {
                        search.begin(next.expect("a ball takes only a vertex it is offered"));
                    }
                    Fed::Heavy => {}
                    Fed::Light => break side,
                }
            };
            let ball = std::mem::take(&mut balls[side]);
            let (union, mass, pads) = if side == 0 {
                (&mut self.plus, &mut mass_plus, &mut pads_plus)
            } else {
                (&mut self.minus, &mut mass_minus, &mut pads_minus)
            };
            for &v in &ball.core {
                union[v] = pid;
            }
            *mass += ball.core_mass;
            let mut pad = ball.core;
            pad.extend(ball.shell);
            pads.push(pad);
        }
        let cover = if 4 * mass_plus >= m {
            let rest: Vec<usize> = x.iter().copied().filter(|&v| self.plus[v] != pid).collect();
            pads_plus
                .into_iter()
                .chain(std::iter::once(rest))
                .map(|y| (y, false))
                .collect()
        } else {
            let rest: Vec<usize> = x
                .iter()
                .copied()
                .filter(|&v| self.minus[v] != pid)
                .collect();
            std::iter::once(rest)
                .chain(pads_minus.into_iter().rev())
                .map(|y| (y, false))
                .collect()
        };
        Ok(cover)
    }

    /// The heavy case of [D] Lemma 4.4 around the center `s`: the lightest shell of width `δ_h`
    /// in `(Δ, 2Δ]` in each direction, and the split of [D] Lemma 4.5.
    fn heavy(&mut self, x: &[usize], id: u64, s: usize, d: &Int) -> Step<Cover, H> {
        let g = self.g;
        let epoch = self.next_id();
        // Marks: `pad_id` in the pad, `core_id` in the core as well.
        let pad_id = self.next_id();
        let core_id = self.next_id();
        let n_h = self.n_h;
        for forward in [true, false] {
            let Solver {
                ell,
                member,
                plus,
                minus,
                outward,
                inward,
                tick,
                scale_h,
                ..
            } = self;
            let (search, union) = if forward {
                (outward, plus)
            } else {
                (inward, minus)
            };
            search.start(epoch, s);
            // The vertices within 2Δ = d/16 and the index of the shell of width δ_h of each.
            let mut reached: Vec<(usize, u64)> = Vec::new();
            while let Some((v, dist)) = search.peek(tick)? {
                if &(&dist + &dist) * &Int::from(8) > *d {
                    break;
                }
                let i = ceil_div(&(&dist * scale_h), d)
                    .to_i128()
                    .and_then(|i| u64::try_from(i).ok())
                    .expect("a distance within 2Δ has a shell index up to 2·N_h");
                search.settle(g, ell, (v, dist), |v| member[v] == id, tick)?;
                reached.push((v, i));
            }
            // Shell `j` holds the indices `n_h + j + 1`, for `j < n_h`. An empty shell is the
            // lightest; otherwise the lightest, the first among equals.
            let mut shells: Vec<(u64, u64)> = reached
                .iter()
                .filter(|&&(_, i)| i > n_h)
                .map(|&(v, i)| (i - n_h - 1, g.mass[v]))
                .collect();
            shells.sort_unstable();
            let mut sums: Vec<(u64, u64)> = Vec::new();
            for (j, w) in shells {
                match sums.last_mut() {
                    Some((k, sum)) if *k == j => *sum += w,
                    _ => sums.push((j, w)),
                }
            }
            let gap = sums
                .iter()
                .enumerate()
                .find(|&(place, &(j, _))| place as u64 != j)
                .map_or(sums.len() as u64, |(place, _)| place as u64);
            let j = if gap < n_h {
                gap
            } else {
                sums.iter()
                    .min_by_key(|&&(j, sum)| (sum, j))
                    .map_or(0, |&(j, _)| j)
            };
            for (v, i) in reached {
                if i <= n_h + j {
                    union[v] = core_id;
                } else if i == n_h + j + 1 {
                    union[v] = pad_id;
                }
            }
        }
        let (plus, minus) = (&self.plus, &self.minus);
        let side_one: Vec<usize> = x
            .iter()
            .copied()
            .filter(|&v| plus[v] >= pad_id && minus[v] != core_id)
            .collect();
        let center: Vec<usize> = x
            .iter()
            .copied()
            .filter(|&v| plus[v] >= pad_id && minus[v] >= pad_id)
            .collect();
        let side_two: Vec<usize> = x.iter().copied().filter(|&v| plus[v] != core_id).collect();
        Ok([(side_one, false), (center, true), (side_two, false)]
            .into_iter()
            .filter(|(y, _)| !y.is_empty())
            .collect())
    }

    /// A potential valid for `c` on `G[x]` from valid potentials on the children, in order, by
    /// the ordered merge of [D] Theorem 3.1.
    fn merge(&mut self, x: &[usize], solved: &[(Vec<usize>, Vec<Int>)]) -> Step<Vec<Int>, H> {
        let g = self.g;
        let id = self.stamp(x);
        for (k, &v) in x.iter().enumerate() {
            self.local[v] = k;
        }
        let local = &self.local;
        let ns = x.len();
        // The memberships of each vertex, in the order of the children, in compressed rows:
        // the child and its potential there.
        let mut mstart = vec![0usize; ns + 1];
        for (y, _) in solved {
            for &v in y {
                mstart[local[v] + 1] += 1;
            }
        }
        for k in 0..ns {
            mstart[k + 1] += mstart[k];
        }
        let total = mstart[ns];
        let mut fill = mstart[..ns].to_vec();
        let mut child = vec![0usize; total];
        let mut phi = vec![Int::ZERO; total];
        for (i, (y, p)) in solved.iter().enumerate() {
            for (&v, pv) in y.iter().zip(p) {
                let slot = &mut fill[local[v]];
                child[*slot] = i;
                phi[*slot] = pv.clone();
                *slot += 1;
            }
        }
        // The offsets α_i ([D] eq. offset): after them no edge into an earlier child has
        // negative reduced weight. `earlier[k]` is the largest shifted potential of `x[k]` in
        // the children seen so far.
        let mut earlier = vec![Int::ZERO; ns];
        let mut alpha = vec![Int::ZERO; solved.len()];
        for (i, (y, p)) in solved.iter().enumerate() {
            let mut a = Int::ZERO;
            for (&u, pu) in y.iter().zip(p) {
                for e in g.out(u) {
                    unit(&mut self.tick)?;
                    let v = g.to[e];
                    if self.member[v] != id || child[mstart[local[v]]] >= i {
                        continue;
                    }
                    let gap = &(&earlier[local[v]] - &self.c[e]) - pu;
                    if gap > a {
                        a = gap;
                    }
                }
            }
            for (&v, pv) in y.iter().zip(p) {
                let k = local[v];
                let shifted = pv + &a;
                if child[mstart[k]] == i || shifted > earlier[k] {
                    earlier[k] = shifted;
                }
            }
            alpha[i] = a;
        }
        for (value, &i) in phi.iter_mut().zip(&child) {
            *value = &*value + &alpha[i];
        }
        // The auxiliary graph ([D] sec. 3.2): node `slot` is a copy, `total + slot` its place
        // on the prefix chain, `2·total + slot` on the suffix chain; `zeta` is each node's
        // potential.
        let mut zeta = vec![Int::ZERO; 3 * total];
        for k in 0..ns {
            let row = mstart[k]..mstart[k + 1];
            let mut high: Option<&Int> = None;
            for slot in row.clone() {
                high = Some(high.map_or(&phi[slot], |h| h.max(&phi[slot])));
                zeta[slot] = phi[slot].clone();
                zeta[total + slot] = high.cloned().unwrap_or(Int::ZERO);
            }
            high = None;
            for slot in row.rev() {
                high = Some(high.map_or(&phi[slot], |h| h.max(&phi[slot])));
                zeta[2 * total + slot] = high.cloned().unwrap_or(Int::ZERO);
            }
        }
        let mut astart = Vec::with_capacity(3 * total + 1);
        let (mut ato, mut aw): (Vec<usize>, Vec<Int>) = (Vec::new(), Vec::new());
        astart.push(0);
        // Connectors: from the copy of `u` in child `i`, for each edge `u → v` of `G[x]`, to the
        // prefix chain of `v` at its last child up to `i`, and to its suffix chain at its first
        // child after `i`. `edges` holds each edge and the place reached in `v`'s row.
        let mut edges: Vec<(usize, usize)> = Vec::new();
        // The copies of the tails of the edges of negative `c`. From a node at its starting label a
        // connector offers its head the head's starting label plus `c` of its edge, and a chain
        // edge offers its head's own starting label, so only these nodes lower a label at first:
        // the nodes [`bf_dijkstra`] starts from.
        let mut seeds: Vec<usize> = Vec::new();
        for (k, &u) in x.iter().enumerate() {
            edges.clear();
            edges.extend(
                g.out(u)
                    .filter(|&e| self.member[g.to[e]] == id)
                    .map(|e| (e, mstart[local[g.to[e]]])),
            );
            let tail = edges.iter().any(|&(e, _)| self.c[e].is_negative());
            for slot in mstart[k]..mstart[k + 1] {
                let i = child[slot];
                if tail {
                    seeds.push(slot);
                }
                for (e, place) in edges.iter_mut() {
                    unit(&mut self.tick)?;
                    let kv = local[g.to[*e]];
                    let (begin, end) = (mstart[kv], mstart[kv + 1]);
                    while *place < end && child[*place] <= i {
                        *place += 1;
                    }
                    let base = &self.c[*e] + &phi[slot];
                    if *place > begin {
                        let node = total + *place - 1;
                        ato.push(node);
                        aw.push(&base - &zeta[node]);
                    }
                    if *place < end {
                        let node = 2 * total + *place;
                        ato.push(node);
                        aw.push(&base - &zeta[node]);
                    }
                }
                astart.push(ato.len());
            }
        }
        for k in 0..ns {
            for slot in mstart[k]..mstart[k + 1] {
                if slot > mstart[k] {
                    ato.push(total + slot - 1);
                    aw.push(&zeta[total + slot] - &zeta[total + slot - 1]);
                }
                ato.push(slot);
                aw.push(&zeta[total + slot] - &phi[slot]);
                astart.push(ato.len());
            }
        }
        for k in 0..ns {
            for slot in mstart[k]..mstart[k + 1] {
                if slot + 1 < mstart[k + 1] {
                    ato.push(2 * total + slot + 1);
                    aw.push(&zeta[2 * total + slot] - &zeta[2 * total + slot + 1]);
                }
                ato.push(slot);
                aw.push(&zeta[2 * total + slot] - &phi[slot]);
                astart.push(ato.len());
            }
        }
        // The source has an edge of weight -ζ to every node: the starting labels.
        let start: Vec<Int> = zeta.iter().map(|z| -z).collect();
        let dist = bf_dijkstra(&astart, &ato, &aw, start, &seeds, self.eta, &mut self.tick)?;
        Ok((0..ns)
            .map(|k| &dist[mstart[k]] + &phi[mstart[k]])
            .collect())
    }
}

/// Distances in the graph `start`, `to`, `w` in compressed rows from a source with an edge of
/// weight `label[x]` to each node `x`, the first round started from `seeds`, by Dijkstra's
/// search on the edges of weight at least 0 with a round of the negative edges after each ([D]
/// Lemma l.129). After round `k` each label is at most the weight of every walk with `k`
/// negative edges besides the source's, so a label
/// that falls in round `eta` shows a walk shorter than all with `eta` negative edges, and the
/// caller's negative cycle ([D] Theorem 3.1). A cycle of parent pointers is a negative cycle
/// (the walk to the root of Cherkassky and Goldberg); it is looked for after each round, from
/// the nodes whose label changed, each node visited once.
fn bf_dijkstra<H>(
    start: &[usize],
    to: &[usize],
    w: &[Int],
    mut label: Vec<Int>,
    seeds: &[usize],
    eta: u64,
    tick: &mut impl FnMut() -> Result<(), H>,
) -> Step<Vec<Int>, H> {
    let n = label.len();
    let mut parent = vec![NONE; n];
    // The first round starts from the nodes `seeds`, which hold every node with an edge that
    // lowers a starting label. Every other node, taken at its starting label, would lower
    // nothing, and a path that lowers a label and starts at it is no shorter than the same path
    // from its next node, so leaving these nodes out changes no label; it saves taking every
    // node of the graph from a heap.
    let mut heap: BinaryHeap<Reverse<(Int, usize)>> = seeds
        .iter()
        .map(|&x| Reverse((label[x].clone(), x)))
        .collect();
    // The round in which a node was last settled, and the walk that last passed it.
    let mut settled_in = vec![0u64; n];
    let mut walked = vec![0u64; n];
    let mut walks = 0u64;
    let (mut settled, mut fell): (Vec<usize>, Vec<usize>) = (Vec::new(), Vec::new());
    let mut round = 0u64;
    loop {
        round += 1;
        settled.clear();
        fell.clear();
        while let Some(Reverse((dx, x))) = heap.pop() {
            unit(tick)?;
            if dx != label[x] || settled_in[x] == round {
                continue;
            }
            settled_in[x] = round;
            settled.push(x);
            for e in start[x]..start[x + 1] {
                unit(tick)?;
                if w[e].is_negative() {
                    continue;
                }
                let y = to[e];
                let candidate = &dx + &w[e];
                if candidate < label[y] {
                    label[y] = candidate.clone();
                    parent[y] = x;
                    heap.push(Reverse((candidate, y)));
                }
            }
        }
        for &x in &settled {
            for e in start[x]..start[x + 1] {
                unit(tick)?;
                if !w[e].is_negative() {
                    continue;
                }
                let y = to[e];
                let candidate = &label[x] + &w[e];
                if candidate < label[y] {
                    label[y] = candidate.clone();
                    parent[y] = x;
                    heap.push(Reverse((candidate, y)));
                    fell.push(y);
                }
            }
        }
        if fell.is_empty() {
            return Ok(label);
        }
        if round >= eta {
            return Err(Stop::Negative);
        }
        let before = walks;
        for &s in settled.iter().chain(&fell) {
            walks += 1;
            let mut v = s;
            while v != NONE && walked[v] <= before {
                unit(tick)?;
                walked[v] = walks;
                v = parent[v];
            }
            if v != NONE && walked[v] == walks {
                return Err(Stop::Negative);
            }
        }
    }
}

/// Where a [`Rounds`] search is within a round.
#[derive(Clone, Copy)]
enum Phase {
    /// Taking the next node from the heap.
    Pop,
    /// Relaxing the `e`th edge of `x`, if its weight is at least 0.
    Relax { x: usize, e: usize },
    /// Relaxing the `e`th edge of `settled[i]`, if its weight is negative.
    Negative { i: usize, e: usize },
}

/// BF-Dijkstra ([D] l.129) on a graph's own weights, from a source joined to each node by an
/// edge of weight 0, one unit of work, a heap entry or an edge, per call of [`Rounds::step`].
/// Round `k` gives each node a label at most the weight of every walk to it with `k` negative
/// edges, so a graph whose shortest paths have few negative edges takes few rounds, each
/// O(E log V), whatever the order of its nodes; a label that falls in round `V` shows a negative
/// cycle, since a simple path has at most `V - 1` edges.
pub struct Rounds<'a> {
    out: &'a [Vec<(usize, Int)>],
    label: Vec<Int>,
    heap: BinaryHeap<Reverse<(Int, usize)>>,
    /// The round in which each node was last settled, and the nodes settled in this one.
    settled_in: Vec<usize>,
    settled: Vec<usize>,
    /// Whether a label fell along a negative edge in this round.
    fell: bool,
    round: usize,
    phase: Phase,
}

impl<'a> Rounds<'a> {
    /// The search of the graph `out`, its edges `u → (v, w)`.
    pub fn new(out: &'a [Vec<(usize, Int)>]) -> Self {
        let n = out.len();
        Rounds {
            out,
            label: vec![Int::ZERO; n],
            heap: (0..n).map(|v| Reverse((Int::ZERO, v))).collect(),
            settled_in: vec![0; n],
            settled: Vec::new(),
            fell: false,
            round: 1,
            phase: Phase::Pop,
        }
    }

    /// One unit of work; once the search ends, the potential, or `None` for a negative cycle.
    pub fn step(&mut self) -> Option<Option<Vec<Int>>> {
        let out = self.out;
        match self.phase {
            Phase::Pop => {
                let Some(Reverse((dx, x))) = self.heap.pop() else {
                    self.phase = Phase::Negative { i: 0, e: 0 };
                    return None;
                };
                if dx == self.label[x] && self.settled_in[x] != self.round {
                    self.settled_in[x] = self.round;
                    self.settled.push(x);
                    self.phase = Phase::Relax { x, e: 0 };
                }
            }
            Phase::Relax { x, e } => {
                let Some((y, w)) = out[x].get(e) else {
                    self.phase = Phase::Pop;
                    return None;
                };
                self.phase = Phase::Relax { x, e: e + 1 };
                if !w.is_negative() {
                    self.lower(x, *y, w);
                }
            }
            Phase::Negative { i, e } => {
                let Some(&x) = self.settled.get(i) else {
                    if !self.fell {
                        return Some(Some(std::mem::take(&mut self.label)));
                    }
                    if self.round >= out.len() {
                        return Some(None);
                    }
                    self.round += 1;
                    self.settled.clear();
                    self.fell = false;
                    self.phase = Phase::Pop;
                    return None;
                };
                let Some((y, w)) = out[x].get(e) else {
                    self.phase = Phase::Negative { i: i + 1, e: 0 };
                    return None;
                };
                self.phase = Phase::Negative { i, e: e + 1 };
                if w.is_negative() && self.lower(x, *y, w) {
                    self.fell = true;
                }
            }
        }
        None
    }

    /// Relaxes the edge `x → y` of weight `w`; whether the label of `y` fell.
    fn lower(&mut self, x: usize, y: usize, w: &Int) -> bool {
        let candidate = &self.label[x] + w;
        if candidate < self.label[y] {
            self.label[y] = candidate.clone();
            self.heap.push(Reverse((candidate, y)));
            return true;
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use std::convert::Infallible;

    use super::{Int, Stop, bf_dijkstra};

    /// A graph `u → (v, w)` in the compressed rows [`bf_dijkstra`] reads.
    fn rows(out: &[Vec<(usize, i64)>]) -> (Vec<usize>, Vec<usize>, Vec<Int>) {
        let mut start = vec![0];
        let (mut to, mut w) = (Vec::new(), Vec::new());
        for edges in out {
            for &(v, x) in edges {
                to.push(v);
                w.push(Int::from(x));
            }
            start.push(to.len());
        }
        (start, to, w)
    }

    /// [`bf_dijkstra`] from labels 0, the first round started from the tails of the negative
    /// edges as [`super::Solver::merge`] starts it, with the round bound `eta`; `None` for a
    /// negative cycle.
    fn search(out: &[Vec<(usize, i64)>], eta: u64) -> Option<Vec<Int>> {
        let (start, to, w) = rows(out);
        let seeds: Vec<usize> = (0..out.len())
            .filter(|&u| out[u].iter().any(|&(_, x)| x < 0))
            .collect();
        let label = vec![Int::ZERO; out.len()];
        match bf_dijkstra(&start, &to, &w, label, &seeds, eta, &mut || {
            Ok::<(), Infallible>(())
        }) {
            Ok(d) => Some(d),
            Err(Stop::Negative) => None,
            Err(Stop::Tick(never)) => match never {},
        }
    }

    /// The reference: Bellman–Ford from labels 0, `n` passes over every edge; a label that
    /// falls in the last pass shows a negative cycle, since a shortest path from the source
    /// joined to each node has at most `n - 1` edges of the graph.
    fn bellman_ford(out: &[Vec<(usize, i64)>]) -> Option<Vec<Int>> {
        let n = out.len();
        let mut d = vec![Int::ZERO; n];
        for pass in 1..=n {
            let mut fell = false;
            for (u, edges) in out.iter().enumerate() {
                for &(v, x) in edges {
                    let to = &d[u] + &Int::from(x);
                    if to < d[v] {
                        d[v] = to;
                        fell = true;
                    }
                }
            }
            if !fell {
                return Some(d);
            }
            if pass == n {
                return None;
            }
        }
        Some(d)
    }

    /// The exit at round `eta` is what reports this cycle. Round 1 starts from node 1 alone,
    /// the one tail of a negative edge, and node 0 falls from it; node 1's parent is still the
    /// source, so the parent walk finds no cycle. In round 2 node 1 falls from node 0 and node 0
    /// from node 1, and the round bound, 2 nodes, is reached before the walk that would close
    /// the cycle.
    #[test]
    fn the_round_bound_reports_a_cycle_before_the_parent_walk() {
        let out = vec![vec![(1, 1)], vec![(0, -2)]];
        assert_eq!(bellman_ford(&out), None);
        assert_eq!(search(&out, 2), None);
    }

    /// A path of `n - 1` negative edges, each falling one round after the one before it,
    /// needs every round up to the bound `n` and is not taken for a cycle.
    #[test]
    fn the_round_bound_lets_the_longest_path_finish() {
        let n = 9;
        let out: Vec<Vec<(usize, i64)>> = (0..n)
            .map(|u| if u == 0 { vec![] } else { vec![(u - 1, -1)] })
            .collect();
        let expected: Vec<Int> = (0..n).map(|u| Int::from(u as i64 + 1 - n as i64)).collect();
        assert_eq!(bellman_ford(&out), Some(expected.clone()));
        assert_eq!(search(&out, n as u64), Some(expected));
    }

    /// 20,000 graphs of 1 to 10 nodes, weights -6 to 9, with the round bound set to the node
    /// count: [`bf_dijkstra`] gives the reference's labels exactly, or reports a negative
    /// cycle exactly when the reference does. Both answers occur.
    #[test]
    fn the_round_bound_agrees_with_bellman_ford() {
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        let mut below = |k: usize| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            (state % k as u64) as usize
        };
        let (mut negative, mut feasible) = (0, 0);
        for _ in 0..20_000 {
            let n = 1 + below(10);
            let mut out: Vec<Vec<(usize, i64)>> = vec![Vec::new(); n];
            for _ in 0..below(3 * n + 1) {
                let (u, v) = (below(n), below(n));
                out[u].push((v, below(16) as i64 - 6));
            }
            let expected = bellman_ford(&out);
            match &expected {
                Some(_) => feasible += 1,
                None => negative += 1,
            }
            assert_eq!(search(&out, n as u64), expected, "graph {out:?}");
        }
        assert!(negative > 1000 && feasible > 1000, "{negative} {feasible}");
    }
}
