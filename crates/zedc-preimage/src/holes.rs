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
//! between them, within the holes of each name that an equality ties to it. Values between
//! the ends of a name of a component with a cycle and a hole may have no point; the ends are
//! exact.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BinaryHeap, VecDeque};

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
    let hi = match greatest(&m.dom, &m.edges, &m.potential, &wide) {
        Ok(u) => u,
        Err(Stop::Empty) => return Outcome::Empty,
        Err(Stop::Refused(names, holed)) => {
            let pick = |set: &[usize]| -> Vec<usize> {
                let set: std::collections::BTreeSet<usize> = set.iter().copied().collect();
                (0..g.dom.len())
                    .filter(|v| set.contains(&m.of[*v].0))
                    .collect()
            };
            return Outcome::Refused {
                names: pick(&names),
                holed: pick(&holed),
            };
        }
    };
    // The negated system: `-x` in the negated integers, each edge reversed.
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
        // The components and the names with holes are those of the system, which was not
        // refused.
        Err(_) => return Outcome::Empty,
    };
    let half = &big * &Int::from(2i64);
    let end = |x: Int| (x.abs() < half).then_some(x);
    Outcome::Kept(
        m.of.iter()
            .map(|(r, o)| {
                let (l, h) = (&lo[*r], &hi[*r]);
                m.dom[*r]
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
    let mut parent: Vec<usize> = (0..n).collect();
    let mut off: Vec<Int> = vec![Int::ZERO; n];
    // The root of `v` and `x_v - x_root`, with the path compressed.
    fn find(parent: &mut [usize], off: &mut [Int], v: usize) -> (usize, Int) {
        let mut path = Vec::new();
        let mut r = v;
        while parent[r] != r {
            path.push(r);
            r = parent[r];
        }
        // From the name nearest the root down, each offset to the root.
        let mut acc = Int::ZERO;
        for &x in path.iter().rev() {
            acc = &acc + &off[x];
            off[x] = acc.clone();
            parent[x] = r;
        }
        (r, off[v].clone())
    }
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
        // x_v = x_u + w.
        let (ru, ou) = find(&mut parent, &mut off, *u);
        let (rv, ov) = find(&mut parent, &mut off, *v);
        if ru == rv {
            if &ov - &ou != *w {
                return None;
            }
        } else {
            // x_rv = x_v - ov = x_u + w - ov = x_ru + ou + w - ov.
            parent[rv] = ru;
            off[rv] = &(&ou + w) - &ov;
        }
    }
    let of: Vec<(usize, Int)> = (0..n).map(|v| find(&mut parent, &mut off, v)).collect();
    let mut index = vec![usize::MAX; n];
    let mut roots = Vec::new();
    for (v, (r, _)) in of.iter().enumerate() {
        if *r == v {
            index[v] = roots.len();
            roots.push(v);
        }
    }
    // Each class's integers: the values every member covers, by one sweep over the members'
    // pieces shifted to the root.
    let mut members = vec![0i64; roots.len()];
    let mut events: Vec<Vec<(Int, i64)>> = vec![Vec::new(); roots.len()];
    for (v, (r, o)) in of.iter().enumerate() {
        members[index[*r]] += 1;
        for (a, b) in &dom[v] {
            events[index[*r]].push((a - o, 1));
            events[index[*r]].push((&(b - o) + &Int::ONE, -1));
        }
    }
    let mut cdom: Vec<Vec<(Int, Int)>> = Vec::with_capacity(roots.len());
    for (mut ev, k) in events.into_iter().zip(members) {
        ev.sort_unstable();
        let mut depth = 0i64;
        let mut open: Option<Int> = None;
        let mut d: Vec<(Int, Int)> = Vec::new();
        for (x, e) in ev {
            depth += e;
            match open.take() {
                None if depth == k => open = Some(x),
                Some(a) if depth < k => d.push((a, &x - &Int::ONE)),
                kept => open = kept,
            }
        }
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

/// Why [`greatest`] stopped: no point, or a component refused, its names and those of them
/// with holes.
enum Stop {
    Empty,
    Refused(Vec<usize>, Vec<usize>),
}

/// The greatest point of a merged system, by its components in topological order. `wide` is
/// past every value the search can reach, finite or not.
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

/// Tarjan's strongly connected components, sources first, without recursion.
fn components(out: &[Vec<(usize, Int)>]) -> Vec<Vec<usize>> {
    let n = out.len();
    let mut index = vec![usize::MAX; n];
    let mut low = vec![0; n];
    let mut on = vec![false; n];
    let mut stack = Vec::new();
    let mut comps = Vec::new();
    let mut next = 0;
    for s in 0..n {
        if index[s] != usize::MAX {
            continue;
        }
        let mut call: Vec<(usize, usize)> = vec![(s, 0)];
        index[s] = next;
        low[s] = next;
        next += 1;
        stack.push(s);
        on[s] = true;
        while let Some(&mut (v, ref mut i)) = call.last_mut() {
            if *i < out[v].len() {
                let z = out[v][*i].0;
                *i += 1;
                if index[z] == usize::MAX {
                    index[z] = next;
                    low[z] = next;
                    next += 1;
                    stack.push(z);
                    on[z] = true;
                    call.push((z, 0));
                } else if on[z] {
                    low[v] = low[v].min(index[z]);
                }
            } else {
                call.pop();
                if let Some(&(p, _)) = call.last() {
                    low[p] = low[p].min(low[v]);
                }
                if low[v] == index[v] {
                    let mut c = Vec::new();
                    while let Some(z) = stack.pop() {
                        on[z] = false;
                        c.push(z);
                        if z == v {
                            break;
                        }
                    }
                    comps.push(c);
                }
            }
        }
    }
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
            // One cycle: each name has one edge in the component.
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
        // part. Test: `l01_39_reduced_product::holes::holes_on_three_names_of_two_cycles_are_refused`.
        // COMPLEXITY.md row S25. A complete solution is an exact method for the snaps on a
        // component with any cycles, or a proof that none is near linear.
        if holed.len() > 2 {
            return Err(Stop::Refused(names.to_vec(), holed));
        }
        self.hull(c, names)?;
        if holed.is_empty() {
            return Ok(());
        }
        // Contraction onto the names with holes (CT): the caps reach each of them through the
        // names without holes, and each reaches the other through those names alone.
        let unholed = |s: &Run, v: usize| !s.holed(v);
        let caps: Vec<(usize, Int)> = names.iter().map(|&v| (v, self.u[v].clone())).collect();
        let reach = self.paths(c, caps.clone(), |s, v| unholed(s, v));
        let cap = |h: usize| reach.get(&h).cloned().unwrap_or_else(|| self.wide.clone());
        let fixed: Vec<(usize, Int)> = match holed[..] {
            [h] => vec![(h, snap_down(&self.dom[h], &cap(h)).ok_or(Stop::Empty)?)],
            [a, b] => {
                let ab = self.paths(c, vec![(a, Int::ZERO)], |s, v| v == a || unholed(s, v));
                let ba = self.paths(c, vec![(b, Int::ZERO)], |s, v| v == b || unholed(s, v));
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
        let all = self.paths(c, sources, |_, _| true);
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
            let found = self.paths(c, caps, |_, _| true);
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
                            // a cycle of negative weight: no point.
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
    /// the potential, which [`Run::hull`] has set at every name of the component.
    fn paths(
        &self,
        c: usize,
        sources: Vec<(usize, Int)>,
        on: impl Fn(&Run, usize) -> bool,
    ) -> BTreeMap<usize, Int> {
        let p = |v: usize| self.potential[v].clone().unwrap_or(Int::ZERO);
        let mut label: BTreeMap<usize, Int> = BTreeMap::new();
        let mut heap: BinaryHeap<Reverse<(Int, usize)>> = BinaryHeap::new();
        for (v, x) in sources {
            if label.get(&v).is_none_or(|y| x < *y) {
                heap.push(Reverse((&x - &p(v), v)));
                label.insert(v, x);
            }
        }
        while let Some(Reverse((k, v))) = heap.pop() {
            let lv = label[&v].clone();
            if &lv - &p(v) != k || !on(self, v) {
                continue;
            }
            for (z, w) in &self.out[v] {
                if self.comp_of[*z] != c {
                    continue;
                }
                let t = &lv + w;
                if label.get(z).is_none_or(|y| t < *y) {
                    heap.push(Reverse((&t - &p(*z), *z)));
                    label.insert(*z, t);
                }
            }
        }
        label
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

    /// A small deterministic generator (a linear congruential one).
    struct Lcg(u64);

    impl Lcg {
        fn next(&mut self, n: u64) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (self.0 >> 33) % n
        }
    }

    /// Random systems of up to five names in `0..=6` with holes, compared with enumeration:
    /// the ends of every name are exact where the method answers, the values kept are a
    /// superset of the exact ones, and no answer is empty where a point exists.
    #[test]
    fn small_systems_agree_with_enumeration() {
        let mut g = Lcg(0x5eed);
        let (mut answered, mut refused) = (0, 0);
        for round in 0..6000 {
            let n = 2 + g.next(4) as usize;
            // Half the systems are a cycle through every name with chords, holes in at most
            // `holed` names, so that cycles and contraction are both reached often.
            let ring = round % 2 == 1;
            let holed = if ring { g.next(4) as usize } else { n };
            let dom: Vec<Vec<(i64, i64)>> = (0..n)
                .map(|i| {
                    let keep: Vec<i64> = if i < holed {
                        (0..=6).filter(|_| g.next(10) < 7).collect()
                    } else {
                        let a = g.next(4) as i64;
                        (a..=a + 2 + g.next(4) as i64).collect()
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
                    edges.push((i, (i + 1) % n, g.next(4) as i64 - 1));
                }
            }
            let m = g.next(if ring { 3 } else { 2 * n as u64 + 1 }) as usize;
            for _ in 0..m {
                let u = g.next(n as u64) as usize;
                let v = g.next(n as u64) as usize;
                edges.push((u, v, g.next(5) as i64 - 2));
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
}
