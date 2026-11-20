//! The ends of names under difference constraints whose names have holes (item ST-holes-moves,
//! cross-review xst round 4, result 1): each name's least and greatest value over the integer
//! points of the constraints, exactly, in O(N log N) in the names, edges and pieces `N`.
//!
//! The constraints are edges `x_v <= x_u + w` between names, each name in a union of intervals.
//! The greatest point is found by the strongly connected components of the edges, in
//! topological order, each from the caps the components before it put on its names:
//!
//! - names tied by two edges of opposite weights, `x_v = x_u + w`, are one name first, in the
//!   intersection of their shifted integers (union-find with offsets), and parallel edges are
//!   one edge of the least weight;
//! - a component of one name is its cap taken down to its integers, O(1) and a search;
//! - a component that is one cycle composes the maps `t -> snap_i(min(c_i, t + w))` round it,
//!   each monotone with slope 0 or 1 on each piece, in one ordered map of pieces, and takes the
//!   greatest `t` with `F(t) >= t`, in O((n + h) log N) for its `n` names and `h` holes
//!   (S11 of the cross-review);
//! - a component of more cycles with at most two names with holes is contracted onto those
//!   names by shortest paths through the others (CT), which leaves a cycle of two names, or one
//!   name, solved as above;
//! - any other component is refused, by the graph and which names have holes alone.
//!
//! The least point is the greatest of the system negated. Every point lies between the two,
//! and each name takes its least and greatest values at them, so its values are its integers
//! between them, within the holes of each name that an equality ties to it: two opposite edges
//! as above, or a cycle of edges of weight 0, found as the cycles of the edges tight at the
//! greatest point (`tie_cycles`). Values between the ends of a name of a component with a
//! cycle of weight above 0 and a hole may have no point; the ends are exact.
//!
//! Proof that the greatest point exists and that every point lies below it: for two points
//! `x`, `y`, `max(x, y)` is a point, since `max(x_v, y_v) <= max(x_u, y_u) + w` at each edge and
//! the larger of two integers of a name is one of its integers (each constraint is max-closed:
//! P. Jeavons and M. C. Cooper, "Tractable constraints on ordered domains", Artificial
//! Intelligence 79(2), 1995, pp. 327-339, doi:10.1016/0004-3702(95)00107-7). So when each
//! name's values are bounded above, the max of the points that each reach one name's greatest
//! value is a point at every name's greatest value; `min` likewise gives the least point. The
//! infinite ends are made finite integers first, which changes no end ([`solve`]). That
//! [`greatest`] finds this point exactly, Empty included, is proved at [`greatest`],
//! [`Run::component`], [`Run::cycle`] and [`Run::hull`]; the negation, at [`solve`].

use std::collections::{BTreeMap, VecDeque};

use zed_graph::{Dijkstra, NegativeReducedWeight, OffsetUnionFind, reduced};
use zedc_int::int::Int;

/// A system of difference constraints: each name's integers and the edges between names.
pub(crate) struct Graph {
    /// Each name's integers, as pieces `(lo, hi)` in increasing order, apart and not adjacent,
    /// `None` an infinite end; at least one piece.
    pub dom: Vec<Vec<(Option<Int>, Option<Int>)>>,
    /// The edges, `(u, v, w)` for `x_v <= x_u + w`.
    pub edges: Vec<(usize, usize, Int)>,
    /// A value of each name at which every edge holds, where one is known.
    pub potential: Vec<Option<Int>>,
}

/// The integers of a name as pieces, `None` an infinite end.
pub(crate) type Pieces = Vec<(Option<Int>, Option<Int>)>;

/// What [`solve`] finds.
#[derive(Debug, PartialEq)]
pub(crate) enum Outcome {
    /// Each name's integers between its least and greatest values.
    Kept(Vec<Pieces>),
    /// No point.
    Empty,
    /// A component of two names or more with holes in `holed` of them that is not one cycle
    /// and has three or more, as indices of the names it holds.
    Refused {
        /// Every name of the component.
        names: Vec<usize>,
        /// Its names with holes.
        holed: Vec<usize>,
    },
}

/// Each name's integers between its least and greatest values over the points of `g`, or why
/// there are none or the method refuses.
pub(crate) fn solve(g: &Graph) -> Outcome {
    // A value as large as any the search can reach from a finite one, so that the infinite
    // ends are integers that stay apart from every finite value: `big` is past each finite end
    // plus the sum of the weights, and the infinities are four times it.
    //
    // Proof that the infinite ends as `-4 big` and `4 big` change no end, and that `end` below
    // tells finite from infinite ones. Write `E` for the sum of `|e|` over the finite ends `e`
    // and `S` for the sum of `|w|` over the edges, so `big = 1 + E + S`.
    // (1) At the greatest point `x` of any such system bounded above, each `x_v` is a top `b`
    // of a piece of some name `s` plus the weight of a simple path of edges tight at `x` from
    // `s` to `v`: let `R` be the names from which `v` is reached by edges tight at `x`; if no
    // name of `R` were at the top of a piece, `x + 1` on `R` would be a point (edges into `R`
    // from outside are not tight, so have slack 1 or more; edges out of `R` only loosen), past
    // `x`. So `|x_v| <= E + S < big` when that top is finite, and `x_v >= 4 big - S > 3 big`
    // when it is the infinity `4 big`; the least point likewise, by negation.
    // (2) No point is lost. Given a point of the system without the bounds `±4 big`, take the
    // greatest point `y` of it below `M`, for `M` past every value of that point; by (1) each
    // `y_v` is `< big` or `>= M - S`. An edge from a name of the first kind `l` to one of the
    // second `h` would need `y_h <= y_l + w < 2 big`, so there is none; taking `M - 4 big` from
    // every `y_h` keeps every edge (within the `h`s each shifts alike; from an `h` to an `l`,
    // `y_l < big <= y_h - S + w` still), and each `y_h` stays above every finite end, in its
    // last piece, now within `4 big`: call it `y'`. The same step at the low ends, negated, on
    // the least point above `-M` of the system with `y'` in it and the tops `4 big`, gives a
    // point `q` within `±4 big`. Now for a name `v`: if its greatest value `g` without the
    // bounds is finite, take `M` past a point at `g`; then `y_v = g` and `v` is of the first
    // kind, so `y'_v = g`, and `max(y', q)` is a point within `±4 big` at `g` (it is no more
    // than `g` at `v`, as `g` is greatest). If `g` is infinite, take a point with `v` past
    // `4 big` and `M` past it: `v` is of the second kind, `y'_v > 3 big`, and `max(y', q)`
    // gives `v` past `3 big` within the bounds. So each finite end is kept, and each infinite
    // one is past `3 big`; the low ends by negation. Empty is kept too: `q` exists exactly
    // when some point does.
    // (3) A finite piece end printed for a name `v` is a finite end `e` of a name `v'` tied to
    // `v` by equalities (a merge or a cycle of weight 0, which hold at every point), plus
    // `x_v - x_v'`, the weight of a simple path of those tight edges, so `|.| <= E + S < big`;
    // an infinite one is `±4 big` plus such a weight, past `3 big`. So `end` below, which keeps
    // values within `2 big`, keeps exactly the finite ends. The merged weights of [`merge`]
    // can add up past `big` along a path of classes, but every value read is of (1) to (3).
    // `wide = 16 big` is past every value: values lie within `±4 big`, a missing path given
    // `wide` as its weight adds `x_b <= x_a + wide`, which `x_a >= -4 big`, `x_b <= 4 big` imply.
    // Test: `tests::infinite_ends_stay_infinite`, `tests::small_systems_agree_with_enumeration`.
    let mut big = Int::ONE;
    for d in &g.dom {
        for (a, b) in d {
            for x in [a, b].into_iter().flatten() {
                big = &big + &x.abs();
            }
        }
    }
    for (_, _, w) in &g.edges {
        big = &big + &w.abs();
    }
    let inf = &big * &Int::from(4i64);
    let lo_of = |x: &Option<Int>| x.clone().unwrap_or_else(|| -&inf);
    let hi_of = |x: &Option<Int>| x.clone().unwrap_or_else(|| inf.clone());
    let dom: Vec<Vec<(Int, Int)>> = g
        .dom
        .iter()
        .map(|d| d.iter().map(|(a, b)| (lo_of(a), hi_of(b))).collect())
        .collect();
    let Some(m) = merge(&dom, &g.edges, &g.potential) else {
        return Outcome::Empty;
    };
    let wide = &inf * &Int::from(4i64);
    // A refusal of merged names, given back as the names of `g` merged into them.
    let refused = |names: &[usize], holed: &[usize]| {
        let pick = |set: &[usize]| -> Vec<usize> {
            let set: std::collections::BTreeSet<usize> = set.iter().copied().collect();
            (0..g.dom.len())
                .filter(|v| set.contains(&m.of[*v].0))
                .collect()
        };
        Outcome::Refused {
            names: pick(names),
            holed: pick(holed),
        }
    };
    let hi = match greatest(&m.dom, &m.edges, &m.potential, &wide) {
        Ok(u) => u,
        Err(Stop::Empty) => return Outcome::Empty,
        Err(Stop::Refused(names, holed)) => return refused(&names, &holed),
    };
    // The negated system: `-x` in the negated integers, each edge reversed. Proof that its
    // greatest point, negated, is the least point: `y = -x` maps the points one to one, as
    // `x_v <= x_u + w` is `y_u <= y_v + w`, the edge `(v, u, w)`, and `x_v in D_v` is
    // `y_v in -D_v`, whose pieces are `(-b, -a)` in reverse order; negation reverses the order,
    // so the greatest `y` is the negated least `x`. A potential `p` holds at `(u, v, w)` when
    // `p_v <= p_u + w`, so exactly when `-p` holds at `(v, u, w)`: `neg_potential` holds where
    // `m.potential` does. The components and the names with holes are the same, reversed.
    let neg_dom: Vec<Vec<(Int, Int)>> = m
        .dom
        .iter()
        .map(|d| d.iter().rev().map(|(a, b)| (-b, -a)).collect())
        .collect();
    let neg_edges: Vec<(usize, usize, Int)> = m
        .edges
        .iter()
        .map(|(u, v, w)| (*v, *u, w.clone()))
        .collect();
    let neg_potential: Vec<Option<Int>> =
        m.potential.iter().map(|p| p.as_ref().map(|p| -p)).collect();
    let lo: Vec<Int> = match greatest(&neg_dom, &neg_edges, &neg_potential, &wide) {
        Ok(u) => u.iter().map(|x| -x).collect(),
        Err(Stop::Empty) => return Outcome::Empty,
        // Never taken. The components and the names with holes are those of the system, which
        // [`greatest`] answered above, so no component has three names with holes or more;
        // and a refusal from [`Run::paths`] cannot come after [`Run::hull`] (proof there): a
        // negated potential that fails at an edge sends `hull` to label correcting, not to a
        // refusal. Kept as a pass-on rather than an `Empty` (commit e275c5f0b).
        Err(Stop::Refused(names, holed)) => return refused(&names, &holed),
    };
    let Some(dom) = tie_cycles(m.dom, &m.edges, &hi) else {
        return Outcome::Empty;
    };
    let half = &big * &Int::from(2i64);
    let end = |x: Int| (x.abs() < half).then_some(x);
    Outcome::Kept(
        m.of.iter()
            .map(|(r, o)| {
                let (l, h) = (&lo[*r], &hi[*r]);
                dom[*r]
                    .iter()
                    .filter(|(a, b)| a <= h && b >= l)
                    .map(|(a, b)| {
                        let a = if a > l { a } else { l };
                        let b = if b < h { b } else { h };
                        (end(a + o), end(b + o))
                    })
                    .collect()
            })
            .collect(),
    )
}

/// The system with names tied by equalities made one: each class's integers, the edges
/// between classes, a potential of each class when its root had one, and each name's class
/// and offset, `x_v = x_class + offset`.
struct Merged {
    dom: Vec<Vec<(Int, Int)>>,
    edges: Vec<(usize, usize, Int)>,
    potential: Vec<Option<Int>>,
    of: Vec<(usize, Int)>,
}

/// Merges the names tied by two edges of opposite weights, `x_v = x_u + w`, by union-find
/// with offsets, each class in the intersection of its names' shifted integers, found by one
/// sweep over their pieces; keeps the least weight of parallel edges. `None` when the merge
/// shows no point. In O((n + m + p) log N) for `p` pieces.
fn merge(
    dom: &[Vec<(Int, Int)>],
    edges: &[(usize, usize, Int)],
    potential: &[Option<Int>],
) -> Option<Merged> {
    let n = dom.len();
    let mut best: BTreeMap<(usize, usize), Int> = BTreeMap::new();
    for (u, v, w) in edges {
        if u == v {
            if w < &Int::ZERO {
                return None;
            }
            continue;
        }
        let e = best.entry((*u, *v)).or_insert_with(|| w.clone());
        if w < e {
            *e = w.clone();
        }
    }
    // Each class's root is the root of its `u` side at the union, which fixes the order of
    // `roots` below and so the classes' numbers.
    let mut uf: OffsetUnionFind<Int> = OffsetUnionFind::new(n);
    for ((u, v), w) in &best {
        if u > v {
            continue;
        }
        let Some(back) = best.get(&(*v, *u)) else {
            continue;
        };
        let sum = w + back;
        if sum < Int::ZERO {
            return None;
        }
        if sum != Int::ZERO {
            continue;
        }
        // x_v = x_u + w; within one class, a difference other than `w` leaves no point.
        if let Err(held) = uf.union_into(*u, *v, w)
            && held != *w
        {
            return None;
        }
    }
    let of: Vec<(usize, Int)> = (0..n).map(|v| uf.find(v)).collect();
    let mut index = vec![usize::MAX; n];
    let mut roots = Vec::new();
    for (v, (r, _)) in of.iter().enumerate() {
        if *r == v {
            index[v] = roots.len();
            roots.push(v);
        }
    }
    // Each class's integers: the values every member covers, shifted to the root.
    let mut members: Vec<Vec<usize>> = vec![Vec::new(); roots.len()];
    for (v, (r, _)) in of.iter().enumerate() {
        members[index[*r]].push(v);
    }
    let mut cdom: Vec<Vec<(Int, Int)>> = Vec::with_capacity(roots.len());
    for vs in &members {
        let d = meet(vs.iter().map(|&v| (&dom[v][..], &of[v].1)));
        if d.is_empty() {
            return None;
        }
        cdom.push(d);
    }
    let mut cedges: BTreeMap<(usize, usize), Int> = BTreeMap::new();
    for ((u, v), w) in &best {
        let (ru, ou) = &of[*u];
        let (rv, ov) = &of[*v];
        // x_v - x_u <= w is x_rv - x_ru <= w - ov + ou.
        let w2 = &(w - ov) + ou;
        let (a, b) = (index[*ru], index[*rv]);
        if a == b {
            if w2 < Int::ZERO {
                return None;
            }
            continue;
        }
        let e = cedges.entry((a, b)).or_insert_with(|| w2.clone());
        if w2 < *e {
            *e = w2;
        }
    }
    Some(Merged {
        dom: cdom,
        edges: cedges.into_iter().map(|((u, v), w)| (u, v, w)).collect(),
        potential: roots.iter().map(|r| potential[*r].clone()).collect(),
        of: of.into_iter().map(|(r, o)| (index[r], o)).collect(),
    })
}

/// The integers every member covers, each member's pieces with its offset `o` taken away
/// (`x - o` for each `x` of it), in increasing order: one sweep over the pieces' ends, in
/// O(p log p) for `p` pieces. Empty when they have no integer in common.
fn meet<'a>(members: impl Iterator<Item = (&'a [(Int, Int)], &'a Int)>) -> Vec<(Int, Int)> {
    let mut k = 0i64;
    let mut events: Vec<(Int, i64)> = Vec::new();
    for (d, o) in members {
        k += 1;
        for (a, b) in d {
            events.push((a - o, 1));
            events.push((&(b - o) + &Int::ONE, -1));
        }
    }
    events.sort_unstable();
    let mut depth = 0i64;
    let mut open: Option<Int> = None;
    let mut out: Vec<(Int, Int)> = Vec::new();
    for (x, e) in events {
        depth += e;
        match open.take() {
            None if depth == k => open = Some(x),
            Some(a) if depth < k => out.push((a, &x - &Int::ONE)),
            kept => open = kept,
        }
    }
    out
}

/// `dom` with the classes a cycle of edges of weight 0 joins made one, as [`merge`] makes one
/// the names two opposite edges tie: each class in the integers every class of its cycle
/// covers, shifted to it. `at` is a point of the system (its greatest). The edges tight at
/// it, `at_v = at_u + w`, are found, and the strongly connected components of those edges:
/// round any cycle of them the weights add up to the sum of `at_v - at_u`, which is 0, so
/// every edge of the cycle holds with equality at every point, and `x_c = x_r + at_c - at_r`
/// for any two classes `r`, `c` of one component. Conversely every edge of a cycle of weight
/// 0 is tight at every point, so every such cycle is found. The equalities show up after the
/// merge: from three edges or more round a cycle, `c - 1 <= a <= b <= c - 1`, or from two
/// that are opposite only once an equality's names are one, `x2 >= x1` and `x3 - x2 >= 3`
/// with `x3 = x1 + 3`; without them the holes of `c` stay out of `a` and `b`
/// (FAIL-linked-holes-scratch-seed, FAIL-linked-sums-between-seed). `None` when a component's
/// classes have no integer in common, so the system has no point.
// Complexity tradeoff: naive version, an implicit equality found by a shortest-path search
// from each name for a cycle of weight 0 back to it, O(n m), or by the closure of the
// constraints. Used: one point of the system, which the search for the greatest point has
// already found, and the components of the edges tight at it (Tarjan 1972,
// doi:10.1137/0201010, full comment in zed-graph `lib.rs`, fn `tarjan`; the same
// `components`), O(n + m), then one sweep per component over its pieces, O(p log p).
// Tradeoffs: none in what is found, as every cycle of weight 0 is tight at any point; the
// tight edges are built once, O(m) memory.
fn tie_cycles(
    mut dom: Vec<Vec<(Int, Int)>>,
    edges: &[(usize, usize, Int)],
    at: &[Int],
) -> Option<Vec<Vec<(Int, Int)>>> {
    let mut tight: Vec<Vec<(usize, Int)>> = vec![Vec::new(); dom.len()];
    for (u, v, w) in edges {
        if at[*v] == &at[*u] + w {
            tight[*u].push((*v, w.clone()));
        }
    }
    for c in components(&tight) {
        let [r, ..] = c[..] else { continue };
        if c.len() == 1 {
            continue;
        }
        // `x_c = x_r + shift_c`.
        let shift: Vec<Int> = c.iter().map(|&v| &at[v] - &at[r]).collect();
        let joint = meet(c.iter().zip(&shift).map(|(&v, s)| (&dom[v][..], s)));
        if joint.is_empty() {
            return None;
        }
        for (&v, s) in c.iter().zip(&shift) {
            dom[v] = joint.iter().map(|(a, b)| (a + s, b + s)).collect();
        }
    }
    Some(dom)
}

/// Why [`greatest`] stopped: no point, or a component refused, its names and those of them
/// with holes.
enum Stop {
    Empty,
    Refused(Vec<usize>, Vec<usize>),
}

/// The greatest point of a merged system, by its components in topological order. `wide` is
/// past every value the search can reach, finite or not.
///
/// Proof, by induction over the components in this order. On entry to a component, `u` at each
/// of its names is the top of its last piece, lowered by `x_u + w` for each edge into it from
/// an earlier component's greatest values `x_u`. If every point lies at or below `x` on the
/// earlier components, every point `y` has `y_v <= y_u + w <= x_u + w`, so `u` bounds every
/// point above; [`Run::component`] then gives the greatest point of the component under `u`,
/// or Empty only when it has none, which is then exact. Its values are at most `u`, so every
/// edge from an earlier component holds, and edges within it hold: the whole is a point at or
/// above every point, the greatest. Edges go only from earlier components to later ones, as
/// [`components`] gives them sources first.
fn greatest(
    dom: &[Vec<(Int, Int)>],
    edges: &[(usize, usize, Int)],
    potential: &[Option<Int>],
    wide: &Int,
) -> Result<Vec<Int>, Stop> {
    let n = dom.len();
    let mut out: Vec<Vec<(usize, Int)>> = vec![Vec::new(); n];
    for (u, v, w) in edges {
        out[*u].push((*v, w.clone()));
    }
    let comps = components(&out);
    let mut comp_of = vec![0; n];
    for (i, c) in comps.iter().enumerate() {
        for &v in c {
            comp_of[v] = i;
        }
    }
    let mut run = Run {
        dom,
        out,
        comp_of,
        u: dom.iter().map(|d| d[d.len() - 1].1.clone()).collect(),
        potential: potential.to_vec(),
        wide,
    };
    for (i, c) in comps.iter().enumerate() {
        run.component(i, c)?;
        for &v in c {
            for (z, w) in &run.out[v] {
                if run.comp_of[*z] != i {
                    let t = &run.u[v] + w;
                    if t < run.u[*z] {
                        run.u[*z] = t;
                    }
                }
            }
        }
    }
    Ok(run.u)
}

/// The strongly connected components of `out` ([`zed_graph::tarjan`]), sources first, the
/// members of each in the order the search completed them, its first node last. R. E. Tarjan,
/// "Depth-first search and linear graph algorithms", SIAM J. Computing 1(2), 1972,
/// pp. 146-160, doi:10.1137/0201010; full comment in zed-graph `lib.rs`, fn `tarjan`. O(n + m).
/// Why sources first: Tarjan completes a component after every component it reaches, so for an
/// edge between components the one it leaves comes after the one it enters, and reversing the
/// list puts it before.
fn components(out: &[Vec<(usize, Int)>]) -> Vec<Vec<usize>> {
    let n = out.len();
    let mut comps = Vec::new();
    zed_graph::tarjan(
        n,
        0..n,
        |v| &out[v],
        |(z, _)| Some(*z),
        |c| {
            c.reverse();
            comps.push(c.to_vec());
        },
    );
    comps.reverse();
    comps
}

/// The greatest integer of `d` at or below `t`.
fn snap_down(d: &[(Int, Int)], t: &Int) -> Option<Int> {
    let i = d.partition_point(|(a, _)| a <= t).checked_sub(1)?;
    let b = &d[i].1;
    Some(if b < t { b.clone() } else { t.clone() })
}

/// The search over one merged system: each name's bound so far, the caps of the components
/// before its own on entry to it and its greatest value after.
struct Run<'a> {
    dom: &'a [Vec<(Int, Int)>],
    out: Vec<Vec<(usize, Int)>>,
    comp_of: Vec<usize>,
    u: Vec<Int>,
    potential: Vec<Option<Int>>,
    wide: &'a Int,
}

impl Run<'_> {
    fn holed(&self, v: usize) -> bool {
        self.dom[v].len() > 1
    }

    fn lo(&self, v: usize) -> &Int {
        &self.dom[v][0].0
    }

    /// Component `c` of `names`: `u` holds their caps on entry, their greatest values on exit.
    fn component(&mut self, c: usize, names: &[usize]) -> Result<(), Stop> {
        if let [v] = names {
            self.u[*v] = snap_down(&self.dom[*v], &self.u[*v]).ok_or(Stop::Empty)?;
            return Ok(());
        }
        let holed: Vec<usize> = names.iter().copied().filter(|&v| self.holed(v)).collect();
        let inner: usize = names
            .iter()
            .map(|&v| {
                self.out[v]
                    .iter()
                    .filter(|(z, _)| self.comp_of[*z] == c)
                    .count()
            })
            .sum();
        if inner == names.len() {
            // One cycle: each name has one edge in the component. Proof: [`merge`] keeps one
            // edge per ordered pair, and in a strongly connected component of two names or
            // more each name has an edge to another name of it, so `inner == n` leaves each
            // name exactly one; following them from `r` reaches every name of the component
            // (it is strongly connected) and comes back to `r`, so the `ok_or` below is never
            // taken.
            let r = holed.first().copied().unwrap_or(names[0]);
            let mut order = vec![r];
            let mut weights = Vec::new();
            loop {
                let v = order[order.len() - 1];
                let (z, w) = self.out[v]
                    .iter()
                    .find(|(z, _)| self.comp_of[*z] == c)
                    .cloned()
                    .ok_or(Stop::Empty)?;
                weights.push(w);
                if z == r {
                    break;
                }
                order.push(z);
            }
            let caps: Vec<Int> = order.iter().map(|&v| self.u[v].clone()).collect();
            let g = self.cycle(&order, &weights, &caps).ok_or(Stop::Empty)?;
            for (v, x) in order.into_iter().zip(g) {
                self.u[v] = x;
            }
            return Ok(());
        }
        // Complexity tradeoff: a component of more than one cycle with holes in three names or
        // more is refused, and the caller narrows it as before this method. What is given up:
        // the exact ends of its names by this method. Why: the snaps of three names or more
        // on two cycles or more interact, and no method in O(N log N) is known for them
        // (cross-review xst, rounds 1 to 4: snapping to a fixed point can take a lap per
        // value of a range, and contraction onto the names with holes leaves a system of
        // three names or more with cycles). Trigger: the graph and which names have holes, not
        // the values: a theta graph, two cycles sharing a path, with a hole in a name of each
        // part. Test: `l01_39_scope_relations::holes::holes_on_three_names_of_two_cycles_are_refused`.
        // COMPLEXITY.md row S25. A complete solution is an exact method for the snaps on a
        // component with any cycles, or a proof that none is near linear.
        // Naive version: snapping to a fixed point, a lap per value of a range, so time in the
        // widths of the ranges, exponential in their bits; used: the refusal, read from the count
        // of names with holes before any snapping.
        if holed.len() > 2 {
            return Err(Stop::Refused(names.to_vec(), holed));
        }
        self.hull(c, names)?;
        if holed.is_empty() {
            return Ok(());
        }
        // Contraction onto the names with holes (CT): the caps reach each of them through the
        // names without holes, and each reaches the other through those names alone.
        //
        // Proof that this is the greatest point under the caps, Empty exact. After `hull`, `u`
        // is the greatest point over the hulls, so every point `y` has `y <= u`, and `u` holds
        // at every edge of the component, so every cycle of it weighs 0 or more. Every edge
        // into a name with holes `h` ends a path whose inner names have no holes, from a name
        // at `u` or from a name with holes; so every point has `y_h <= U_h` (`reach`, the least
        // `u_s` plus the path's weight over such paths from any `s`) and, for two of them,
        // `y_b <= y_a + d_ab`, `y_a <= y_b + d_ba` (`ab`, `ba`, over paths whose inner names
        // have no holes; `wide` where there is none, a bound every value meets). A path from
        // `h` back to `h` alone weighs 0 or more, so adds nothing. With `[h]`, `snap_down` of
        // `U_h` bounds `y_h`; with `[a, b]`, [`Run::cycle`] gives the greatest point of these
        // bounds on the two names. Every point is at or below those values `g`, and below the
        // least distances `all` from the caps of the names without holes and from `g`.
        // Conversely `all` is a point: at a name with holes `all = g`, since a path into it
        // from a cap of a name without holes, cut at its last name with holes, is either one
        // of `reach`'s (at least `U_h >= g_h`), or `g` of that name plus a path of `ab`/`ba`
        // or a cycle (at least `g_h`, as `g` holds at the bounds of two names); every edge
        // into a name without holes holds by the least distances, and every edge into a name
        // with holes by the same cut; a name without holes is one piece, at most its cap, so
        // only `lo` is checked, and when `all` is below it every point is too: no point.
        // All `map_err` here are never taken: `hull` set the potential to `u`, which holds at
        // every edge of the component ([`Run::paths`]). Test:
        // `tests::small_systems_agree_with_enumeration`; the system tests of
        // `l01_39_scope_relations::holes` (CE-A, the slot booking).
        let unholed = |s: &Run, v: usize| !s.holed(v);
        let caps: Vec<(usize, Int)> = names.iter().map(|&v| (v, self.u[v].clone())).collect();
        let reach =
            (self.paths(c, caps.clone(), |s, v| unholed(s, v))).map_err(|_| self.refuse(names))?;
        let cap = |h: usize| reach.get(&h).cloned().unwrap_or_else(|| self.wide.clone());
        let fixed: Vec<(usize, Int)> = match holed[..] {
            [h] => vec![(h, snap_down(&self.dom[h], &cap(h)).ok_or(Stop::Empty)?)],
            [a, b] => {
                let ab = (self.paths(c, vec![(a, Int::ZERO)], |s, v| v == a || unholed(s, v)))
                    .map_err(|_| self.refuse(names))?;
                let ba = (self.paths(c, vec![(b, Int::ZERO)], |s, v| v == b || unholed(s, v)))
                    .map_err(|_| self.refuse(names))?;
                let w = |m: &BTreeMap<usize, Int>, z: usize| {
                    m.get(&z).cloned().unwrap_or_else(|| self.wide.clone())
                };
                let g = self
                    .cycle(&[a, b], &[w(&ab, b), w(&ba, a)], &[cap(a), cap(b)])
                    .ok_or(Stop::Empty)?;
                vec![(a, g[0].clone()), (b, g[1].clone())]
            }
            _ => Vec::new(),
        };
        // The names without holes take their greatest values from the caps and the names
        // with holes, by one search; the names with holes keep theirs.
        let mut sources: Vec<(usize, Int)> =
            caps.into_iter().filter(|(v, _)| !self.holed(*v)).collect();
        sources.extend(fixed.iter().cloned());
        let all = (self.paths(c, sources, |_, _| true)).map_err(|_| self.refuse(names))?;
        for &v in names {
            let x = all.get(&v).cloned().unwrap_or_else(|| self.u[v].clone());
            if x < *self.lo(v) {
                return Err(Stop::Empty);
            }
            self.u[v] = x;
        }
        Ok(())
    }

    /// The greatest values of the cycle `order`, the edge from each name to the next of weight
    /// `weights[i]`, the last back to the first, each name capped by `caps[i]`: the map round
    /// the cycle from the first name, `t -> snap(min(c, t + w))` at each name, is built in one
    /// ordered map of pieces, and its greatest `t` with `F(t) >= t` is the first name's value.
    ///
    /// Proof (S11 of the cross-review xst). Let `g_0(t) = snap_0(t)`, `g_i(t) =
    /// snap_i(min(c_i, g_(i-1)(t) + w_(i-1)))` and `F(t) = snap_0(min(c_0, g_(n-1)(t) + w_(n-1)))`,
    /// `snap_i` the greatest integer of name `i` at or below its input; each is monotone, as
    /// `+ w`, `min(c, .)` and `snap` are, and the inputs where one has no value are the least
    /// ones, cut off by `from` (no point has its first name there, since its others would be
    /// lower still). Let `t*` be the greatest `t` in `from..=c_0` with `F(t) >= t`. (a) `t*` is
    /// an integer of name 0 and `F(t*) = t*`: if `F(t*) > t*`, then `t' = F(t*) <= c_0` has
    /// `F(t') >= F(t*) = t'`, past `t*`. (b) `x_0 = t*`, `x_i = g_i(t*)` is a point: each `x_i`
    /// is an integer of its name at most `c_i`, the edge into each `i >= 1` holds by its `min`,
    /// and the closing edge by `t* = F(t*) <= g_(n-1)(t*) + w_(n-1)`. (c) Every point `y` under
    /// the caps has `y_i <= g_i(y_0)`, by induction with monotonicity, so `y_0 <= F(y_0)`, so
    /// `y_0 <= t*` and `y_i <= g_i(t*) = x_i`. `None` only when no `t` has `F(t) >= t`: no point.
    /// [`Map::greatest_fixpoint`] scans the pieces from the top: on a constant piece of output
    /// `v` the greatest such `t` is `min(hi, v)` if at least the piece's `lo`, and on a shift
    /// piece every `t` has it when the shift is 0 or more, none otherwise. Cost: each `cap` or
    /// `snap` gap is one `flatten`, which removes the pieces it meets and adds at most three,
    /// so the pieces ever made are O(n + h), each at O(log N): O((n + h) log N).
    fn cycle(&self, order: &[usize], weights: &[Int], caps: &[Int]) -> Option<Vec<Int>> {
        let d = |v: usize| &self.dom[v];
        let r = order[0];
        let mut map = Map::identity(d(r)[0].0.clone(), caps[0].clone(), self.wide);
        map.snap(d(r));
        for i in 1..order.len() {
            map.off = &map.off + &weights[i - 1];
            map.cap(&caps[i]);
            map.snap(d(order[i]));
        }
        map.off = &map.off + &weights[order.len() - 1];
        map.cap(&caps[0]);
        map.snap(d(r));
        let t = map.greatest_fixpoint()?;
        let mut g = vec![t];
        for i in 1..order.len() {
            let x = &g[i - 1] + &weights[i - 1];
            let x = if x < caps[i] { x } else { caps[i].clone() };
            g.push(snap_down(d(order[i]), &x)?);
        }
        Some(g)
    }

    /// The greatest values of the names of component `c` over their hulls, from their caps:
    /// by Dijkstra on the reduced weights when the potential holds at every edge of the
    /// component, otherwise by label correcting. The values found are then the potential.
    /// Dijkstra 1959, doi:10.1007/BF01386390, and Bellman 1958, doi:10.1090/qam/102435; the
    /// full comments are at the heads of zed-graph `heap.rs` and `worklist.rs`.
    ///
    /// Complexity tradeoff: without a potential at every name of the component, label
    /// correcting (Bellman–Ford with a queue) costs O(n m) at worst on the component's `n`
    /// names and `m` edges, where Dijkstra costs O(m log n). What is given up: the bound
    /// O(N log N) on such components. Why: the greatest point of difference constraints with
    /// negative weights needs shortest paths with negative weights, and a potential is what
    /// makes them Dijkstra's. Trigger: a component of more than one cycle that the scope's
    /// potential does not hold at, as after a projection of every block, which empties it
    /// (`Scope::reseed`). Test: `holes::tests::small_systems_agree_with_enumeration`.
    /// COMPLEXITY.md row S25. A complete solution passes the point the scope's solver finds
    /// for each tree as the potential.
    fn hull(&mut self, c: usize, names: &[usize]) -> Result<(), Stop> {
        let holds = names.iter().all(|&v| {
            self.potential[v].as_ref().is_some_and(|pv| {
                self.out[v].iter().all(|(z, w)| {
                    self.comp_of[*z] != c
                        || self.potential[*z]
                            .as_ref()
                            .is_some_and(|pz| &(w + pv) - pz >= Int::ZERO)
                })
            })
        });
        if holds {
            let caps: Vec<(usize, Int)> = names.iter().map(|&v| (v, self.u[v].clone())).collect();
            let found = (self.paths(c, caps, |_, _| true)).map_err(|_| self.refuse(names))?;
            for &v in names {
                if let Some(x) = found.get(&v) {
                    self.u[v] = x.clone();
                }
            }
        } else {
            let mut queue: VecDeque<usize> = names.iter().copied().collect();
            let mut queued: BTreeMap<usize, usize> = names.iter().map(|&v| (v, 1)).collect();
            let mut inq: std::collections::BTreeSet<usize> = names.iter().copied().collect();
            while let Some(v) = queue.pop_front() {
                inq.remove(&v);
                for i in 0..self.out[v].len() {
                    let (z, w) = &self.out[v][i];
                    let z = *z;
                    if self.comp_of[z] != c {
                        continue;
                    }
                    let t = &self.u[v] + w;
                    if t < self.u[z] {
                        if t < *self.lo(z) {
                            return Err(Stop::Empty);
                        }
                        self.u[z] = t;
                        if inq.insert(z) {
                            let k = queued.entry(z).or_insert(0);
                            *k += 1;
                            // A name queued more times than the component has names lies on
                            // a cycle of negative weight: no point. Proof that no system with
                            // a point gets here: count passes of the queue, pass 0 the names
                            // queued first. After pass `j` each label is at most the least cap
                            // plus the weight of a path of `j + 1` edges or fewer; with no
                            // cycle of negative weight the least over all paths is reached by
                            // a simple one, of `n - 1` edges at most, so no label falls in pass
                            // `n - 1` or after, and a name is queued at most once per pass
                            // (`inq`): at most `1 + (n - 1) = n` times. With such a cycle the
                            // labels on it fall without end, so this or the `lo` test above
                            // ends the loop; the `lo` test is exact as labels only fall and
                            // each bounds every point.
                            if *k > names.len() {
                                return Err(Stop::Empty);
                            }
                            queue.push_back(z);
                        }
                    }
                }
            }
        }
        for &v in names {
            if self.u[v] < *self.lo(v) {
                return Err(Stop::Empty);
            }
            self.potential[v] = Some(self.u[v].clone());
        }
        Ok(())
    }

    /// Least distances within component `c` from `sources`, each with its starting value,
    /// going on from a name only where `on` allows it, by Dijkstra on the reduced weights of
    /// the potential, which [`Run::hull`] has set at every name of the component. Dijkstra
    /// 1959, doi:10.1007/BF01386390; the full comment is at the head of zed-graph `heap.rs`.
    ///
    /// The search keeps each name's label less its potential, a distance over the reduced
    /// weights `w + p(v) - p(z)`, and adds the potential back at the end. An edge whose reduced
    /// weight is below zero is `Err`: the potential does not hold there, and the search would
    /// no longer take each name once, so its O(m log n) would not hold either. The caller
    /// refuses the component ([`Run::refuse`]).
    ///
    /// Proof that no caller gets `Err`: `hull` calls this only when the potential holds at
    /// every edge of the component (`holds`), and on return sets the potential to `u`, the
    /// least distances from the caps, which satisfy `u_z <= u_v + w` at every edge of the
    /// component; every later call, in [`Run::component`], comes after `hull`. So each reduced
    /// weight is 0 or more and every `map_err(|_| self.refuse(..))` is never taken.
    fn paths(
        &self,
        c: usize,
        sources: Vec<(usize, Int)>,
        on: impl Fn(&Run, usize) -> bool,
    ) -> Result<BTreeMap<usize, Int>, NegativeReducedWeight> {
        let p = |v: usize| self.potential[v].clone().unwrap_or(Int::ZERO);
        let mut search = Dijkstra::new(BTreeMap::new());
        for (v, x) in sources {
            search.lower(v, &x - &p(v));
        }
        while let Some((k, v)) = search.pop() {
            if !on(self, v) {
                continue;
            }
            let pv = p(v);
            for (z, w) in &self.out[v] {
                if self.comp_of[*z] != c {
                    continue;
                }
                let r = reduced(&(w + &pv) - &p(*z), &Int::ZERO)?;
                search.lower(*z, &k + &r);
            }
        }
        Ok(search
            .into_labels()
            .into_iter()
            .map(|(v, k)| (v, &k + &p(v)))
            .collect())
    }

    /// The refusal of the component of `names`, its names and those of them with holes.
    fn refuse(&self, names: &[usize]) -> Stop {
        let holed = names.iter().copied().filter(|&v| self.holed(v)).collect();
        Stop::Refused(names.to_vec(), holed)
    }
}

/// The output on a piece of inputs: a constant, or the input plus a shift.
#[derive(Clone, Debug)]
enum Out {
    Const(Int),
    Shift(Int),
}

/// A piece of a monotone map: its inputs `lo..=hi` and its raw output.
#[derive(Clone, Debug)]
struct Piece {
    lo: Int,
    hi: Int,
    out: Out,
}

impl Piece {
    fn out_lo(&self) -> Int {
        match &self.out {
            Out::Const(c) => c.clone(),
            Out::Shift(s) => &self.lo + s,
        }
    }

    fn out_hi(&self) -> Int {
        match &self.out {
            Out::Const(c) => c.clone(),
            Out::Shift(s) => &self.hi + s,
        }
    }
}

/// A monotone map from the inputs `from..=` its last piece to the integers, of slope 0 or 1
/// on each piece. The output is the raw output plus `off`, so adding a weight is O(1). The
/// pieces are keyed by their raw output at their least input, then that input, which orders
/// them by input and by output at once.
struct Map {
    pieces: BTreeMap<(Int, Int), Piece>,
    off: Int,
    from: Int,
    /// Past every input and raw output.
    wide: Int,
}

impl Map {
    fn identity(from: Int, top: Int, wide: &Int) -> Map {
        let mut pieces = BTreeMap::new();
        if from <= top {
            let p = Piece {
                lo: from.clone(),
                hi: top,
                out: Out::Shift(Int::ZERO),
            };
            pieces.insert((p.out_lo(), p.lo.clone()), p);
        }
        Map {
            pieces,
            off: Int::ZERO,
            from,
            wide: wide.clone(),
        }
    }

    fn insert(&mut self, p: Piece) {
        self.pieces.insert((p.out_lo(), p.lo.clone()), p);
    }

    /// The pieces whose output meets `a..=b`, in input order.
    fn meeting(&self, a: &Int, b: &Int) -> Vec<Piece> {
        let (ra, rb) = (a - &self.off, b - &self.off);
        let low = -&self.wide;
        let mut out: Vec<Piece> = Vec::new();
        if let Some((_, p)) = self.pieces.range(..(ra.clone(), low.clone())).next_back()
            && p.out_hi() >= ra
        {
            out.push(p.clone());
        }
        out.extend(
            self.pieces
                .range((ra, low)..=(rb, self.wide.clone()))
                .map(|(_, p)| p.clone()),
        );
        out
    }

    /// Replaces the outputs in `a..=b` by `to`; with `None`, by no value, where `a..=b` starts
    /// below every output, so that the inputs it takes are the least ones.
    fn flatten(&mut self, a: &Int, b: &Int, to: Option<Int>) {
        if a > b {
            return;
        }
        let hit = self.meeting(a, b);
        let (Some(first), Some(last)) = (hit.first().cloned(), hit.last().cloned()) else {
            return;
        };
        let (ra, rb) = (a - &self.off, b - &self.off);
        let mut lo_in = first.lo.clone();
        let mut hi_in = last.hi.clone();
        for p in &hit {
            self.pieces.remove(&(p.out_lo(), p.lo.clone()));
        }
        // The parts of the end pieces outside `a..=b` stay.
        if let Out::Shift(s) = &first.out
            && &first.lo + s < ra
        {
            let cut = &ra - s;
            self.insert(Piece {
                lo: first.lo.clone(),
                hi: &cut - &Int::ONE,
                out: first.out.clone(),
            });
            lo_in = cut;
        }
        if let Out::Shift(s) = &last.out
            && &last.hi + s > rb
        {
            let cut = &rb - s;
            self.insert(Piece {
                lo: &cut + &Int::ONE,
                hi: last.hi.clone(),
                out: last.out.clone(),
            });
            hi_in = cut;
        }
        match to {
            Some(c) => self.insert(Piece {
                lo: lo_in,
                hi: hi_in,
                out: Out::Const(&c - &self.off),
            }),
            None => {
                let next = &hi_in + &Int::ONE;
                if next > self.from {
                    self.from = next;
                }
            }
        }
    }

    /// `t -> min(c, map(t))`.
    fn cap(&mut self, c: &Int) {
        let wide = self.wide.clone();
        self.flatten(&(c + &Int::ONE), &wide, Some(c.clone()));
    }

    /// `t -> snap_d(map(t))`: each gap of `d` taken to the value below it, every output below
    /// `d` to none. In O(g log N) for the `g` gaps of `d` and the pieces removed.
    fn snap(&mut self, d: &[(Int, Int)]) {
        let low = -&self.wide;
        self.flatten(&low, &(&d[0].0 - &Int::ONE), None);
        for w in d.windows(2) {
            self.flatten(
                &(&w[0].1 + &Int::ONE),
                &(&w[1].0 - &Int::ONE),
                Some(w[0].1.clone()),
            );
        }
    }

    /// The greatest input `t` at or above `from` with `map(t) >= t`.
    fn greatest_fixpoint(&self) -> Option<Int> {
        for p in self.pieces.values().rev() {
            if p.hi < self.from {
                continue;
            }
            let lo = if p.lo > self.from { &p.lo } else { &self.from };
            match &p.out {
                Out::Const(c) => {
                    let v = c + &self.off;
                    let t = if p.hi < v { p.hi.clone() } else { v };
                    if t >= *lo {
                        return Some(t);
                    }
                }
                Out::Shift(s) => {
                    if s + &self.off >= Int::ZERO {
                        return Some(p.hi.clone());
                    }
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every point of `g` by enumeration over its finite ranges, each name's values.
    fn brute(dom: &[Vec<(i64, i64)>], edges: &[(usize, usize, i64)]) -> Option<Vec<Vec<i64>>> {
        let vals: Vec<Vec<i64>> = dom
            .iter()
            .map(|d| d.iter().flat_map(|&(a, b)| a..=b).collect())
            .collect();
        let n = dom.len();
        let mut seen: Vec<std::collections::BTreeSet<i64>> = vec![Default::default(); n];
        let mut idx = vec![0usize; n];
        let mut any = false;
        loop {
            let p: Vec<i64> = (0..n).map(|i| vals[i][idx[i]]).collect();
            if edges.iter().all(|&(u, v, w)| p[v] - p[u] <= w) {
                any = true;
                for (s, x) in seen.iter_mut().zip(&p) {
                    s.insert(*x);
                }
            }
            let mut i = 0;
            while i < n && idx[i] + 1 == vals[i].len() {
                idx[i] = 0;
                i += 1;
            }
            if i == n {
                break;
            }
            idx[i] += 1;
        }
        any.then(|| seen.into_iter().map(|s| s.into_iter().collect()).collect())
    }

    fn graph(dom: &[Vec<(i64, i64)>], edges: &[(usize, usize, i64)]) -> Graph {
        Graph {
            dom: dom
                .iter()
                .map(|d| {
                    d.iter()
                        .map(|&(a, b)| (Some(Int::from(a)), Some(Int::from(b))))
                        .collect()
                })
                .collect(),
            edges: edges
                .iter()
                .map(|&(u, v, w)| (u, v, Int::from(w)))
                .collect(),
            potential: vec![None; dom.len()],
        }
    }

    /// `paths` on a cycle `0 → 1 → 2 → 0` of weights 5, -4 and 0: with a potential that holds
    /// at each edge, the least distances from 0 at 10; with one that does not (all 0, so the
    /// edge `1 → 2` has reduced weight -4), `Err`. The search before `zed_graph::Dijkstra`
    /// returned the distances there too, taking a name again each time its label fell, which
    /// is label correcting and not O(m log n).
    #[test]
    fn paths_refuse_a_potential_that_does_not_hold() {
        let wide = Int::from(1_000i64);
        let dom: Vec<Vec<(Int, Int)>> = vec![vec![(Int::from(-100i64), Int::from(100i64))]; 3];
        let edge = |z: usize, w: i64| vec![(z, Int::from(w))];
        let run = |p: [i64; 3]| Run {
            dom: &dom,
            out: vec![edge(1, 5), edge(2, -4), edge(0, 0)],
            comp_of: vec![0; 3],
            u: vec![Int::ZERO; 3],
            potential: p.iter().map(|&x| Some(Int::from(x))).collect(),
            wide: &wide,
        };
        let from = || vec![(0, Int::from(10i64))];
        let found = run([0, 5, 1]).paths(0, from(), |_, _| true);
        let want: BTreeMap<usize, Int> = [(0, 10i64), (1, 15), (2, 11)]
            .map(|(v, x)| (v, Int::from(x)))
            .into();
        assert_eq!(found, Ok(want));
        assert_eq!(
            run([0; 3]).paths(0, from(), |_, _| true),
            Err(NegativeReducedWeight)
        );
    }

    /// Random systems of up to five names in `0..=6` with holes, compared with enumeration:
    /// the ends of every name are exact where the method answers, the values kept are a
    /// superset of the exact ones, and no answer is empty where a point exists.
    #[test]
    fn small_systems_agree_with_enumeration() {
        let mut g = crate::seed::Rng::new(0x5eed);
        let (mut answered, mut refused) = (0, 0);
        for round in 0..6000 {
            let n = 2 + g.below_u64(4) as usize;
            // Half the systems are a cycle through every name with chords, holes in at most
            // `holed` names, so that cycles and contraction are both reached often.
            let ring = round % 2 == 1;
            let holed = if ring { g.below_u64(4) as usize } else { n };
            let dom: Vec<Vec<(i64, i64)>> = (0..n)
                .map(|i| {
                    let keep: Vec<i64> = if i < holed {
                        (0..=6).filter(|_| g.below_u64(10) < 7).collect()
                    } else {
                        let a = g.below_u64(4) as i64;
                        (a..=a + 2 + g.below_u64(4) as i64).collect()
                    };
                    let mut d: Vec<(i64, i64)> = Vec::new();
                    for v in keep {
                        match d.last_mut() {
                            Some((_, b)) if *b + 1 == v => *b = v,
                            _ => d.push((v, v)),
                        }
                    }
                    if d.is_empty() {
                        d.push((3, 3));
                    }
                    d
                })
                .collect();
            let mut edges: Vec<(usize, usize, i64)> = Vec::new();
            if ring {
                for i in 0..n {
                    edges.push((i, (i + 1) % n, g.below_u64(4) as i64 - 1));
                }
            }
            let m = g.below_u64(if ring { 3 } else { 2 * n as u64 + 1 }) as usize;
            for _ in 0..m {
                let u = g.below_u64(n as u64) as usize;
                let v = g.below_u64(n as u64) as usize;
                edges.push((u, v, g.below_u64(5) as i64 - 2));
            }
            let exact = brute(&dom, &edges);
            match (solve(&graph(&dom, &edges)), exact) {
                (Outcome::Empty, None) => answered += 1,
                (Outcome::Kept(kept), Some(exact)) => {
                    answered += 1;
                    for (k, e) in kept.iter().zip(&exact) {
                        let values: Vec<i64> = k
                            .iter()
                            .flat_map(|(a, b)| {
                                let a = a.as_ref().and_then(Int::to_i128).expect("finite") as i64;
                                let b = b.as_ref().and_then(Int::to_i128).expect("finite") as i64;
                                a..=b
                            })
                            .collect();
                        assert_eq!(values.first(), e.first(), "{dom:?} {edges:?}");
                        assert_eq!(values.last(), e.last(), "{dom:?} {edges:?}");
                        assert!(e.iter().all(|x| values.contains(x)), "{dom:?} {edges:?}");
                    }
                }
                (Outcome::Refused { .. }, _) => refused += 1,
                (got, exact) => panic!("{dom:?} {edges:?}: {got:?} against {exact:?}"),
            }
        }
        assert!(answered > 5000, "{answered} answered, {refused} refused");
    }

    /// An infinite end stays infinite, and a finite one bounds through an edge.
    #[test]
    fn infinite_ends_stay_infinite() {
        let g = Graph {
            dom: vec![
                vec![(None, Some(Int::from(3i64))), (Some(Int::from(5i64)), None)],
                vec![(Some(Int::ZERO), Some(Int::from(10i64)))],
            ],
            edges: vec![(1, 0, Int::ZERO), (0, 1, Int::from(2i64))],
            potential: vec![None, None],
        };
        let Outcome::Kept(k) = solve(&g) else {
            panic!("no answer")
        };
        assert_eq!(
            k[0],
            vec![
                (Some(Int::from(-2i64)), Some(Int::from(3i64))),
                (Some(Int::from(5i64)), Some(Int::from(10i64)))
            ]
        );
    }

    /// The values of each name `solve` keeps, all finite.
    fn kept(dom: &[Vec<(i64, i64)>], edges: &[(usize, usize, i64)]) -> Vec<Vec<i64>> {
        let Outcome::Kept(k) = solve(&graph(dom, edges)) else {
            panic!("no answer: {dom:?} {edges:?}")
        };
        k.iter()
            .map(|d| {
                d.iter()
                    .flat_map(|(a, b)| {
                        let a = a.as_ref().and_then(Int::to_i128).expect("finite") as i64;
                        let b = b.as_ref().and_then(Int::to_i128).expect("finite") as i64;
                        a..=b
                    })
                    .collect()
            })
            .collect()
    }

    /// A cycle of three edges of weight 0, `c - 1 <= a <= b <= c - 1`, ties `a` and `b` to
    /// `c` as an equality would, so the hole of `c` in `{0, 2}` is in them, and through the
    /// equality `d = a - 1` in `d` too (FAIL-linked-holes-scratch-seed: the hulls `-1..=1`
    /// were kept, since only two opposite edges were read as an equality).
    #[test]
    fn a_cycle_of_weight_0_ties_its_names_as_an_equality_does() {
        let dom = [
            vec![(-1, 1)],
            vec![(-1, 1)],
            vec![(0, 0), (2, 2)],
            vec![(-2, 0)],
        ];
        let edges = [(0, 2, 1), (1, 0, 0), (2, 1, -1), (0, 3, -1), (3, 0, 1)];
        let exact = brute(&dom, &edges).expect("a point");
        assert_eq!(exact, [vec![-1, 1], vec![-1, 1], vec![0, 2], vec![-2, 0]]);
        assert_eq!(kept(&dom, &edges), exact);
    }

    /// Two edges between a name and an equality's other names, `x2 >= x1` and
    /// `x3 - x2 >= 3` with `x3 = x1 + 3`, are opposite only once the equality is merged, and
    /// tie `x2` to `x1` with its hole, on unbounded names (FAIL-linked-sums-between-seed:
    /// `x2` was kept whole).
    #[test]
    fn edges_opposite_after_a_merge_tie_their_names() {
        let i = |x: i64| Some(Int::from(x));
        let all = vec![(None, None)];
        let g = Graph {
            dom: vec![
                vec![(None, i(1)), (i(3), None)],
                all.clone(),
                all.clone(),
                all,
            ],
            edges: [
                (0, 1, 2),
                (1, 0, -2),
                (1, 3, 3),
                (3, 1, -3),
                (2, 1, 0),
                (3, 2, -3),
            ]
            .map(|(u, v, w)| (u, v, Int::from(w)))
            .to_vec(),
            potential: vec![None; 4],
        };
        let Outcome::Kept(k) = solve(&g) else {
            panic!("no answer")
        };
        assert_eq!(k[2], vec![(None, i(3)), (i(5), None)]);
        assert_eq!(k[1], k[2]);
        assert_eq!(k[3], vec![(None, i(6)), (i(8), None)]);
    }

    /// Control: a cycle of weight 1 ties nothing, and the hole of `c` stays in `c` alone, as
    /// enumeration finds.
    #[test]
    fn a_cycle_of_weight_1_ties_nothing() {
        let dom = [vec![(-1, 1)], vec![(0, 0), (2, 2)]];
        let edges = [(0, 1, 1), (1, 0, 0)];
        let exact = brute(&dom, &edges).expect("a point");
        assert_eq!(exact, [vec![-1, 0, 1], vec![0, 2]]);
        assert_eq!(kept(&dom, &edges), exact);
    }
}
