//! The reference models of META4 result 1, run against enumeration. They are not `Scope`:
//! they hold the answers that item ST-holes-moves must reach, and the negative controls show
//! that each check can fail.
//!
//! - SCC composition (Codex round 4, `work/r4/src/lib.rs`): the exact greatest solution of a
//!   difference system whose strongly connected components are single names or simple
//!   cycles, by composing each cycle's piecewise map once; any other component is refused by
//!   its shape alone.
//! - Closure and snapping (Codex round 3, `holes.mjs`): all-pairs distances, then relaxing
//!   and snapping each name below its cap to a value it may hold until nothing changes; each
//!   name's set by repeated capped queries.
//!
//! Gemini's CS and CT models (round 4, `q1_holes_r4.rs`) and Claude's `holes4` checker compute
//! the same answers as these two and are covered by them; their controls are ported below.

use std::collections::{BTreeMap, VecDeque};
use std::ops::Bound::{Included, Unbounded};

use super::{Inst, Lcg};
use zed_tests::scaling;

/// A sorted union of disjoint, non-adjacent runs of integers.
type Domain = Vec<(i64, i64)>;

/// Names with domains; edge `(u, v, w)` is `x_v <= x_u + w`, as in [`Inst`].
#[derive(Clone, Debug)]
struct System {
    domains: Vec<Domain>,
    edges: Vec<(usize, usize, i64)>,
}

/// The runs of sorted, distinct `values`.
fn domain(values: impl IntoIterator<Item = i64>) -> Domain {
    let mut out: Domain = vec![];
    for v in values {
        match out.last_mut() {
            Some((_, h)) if *h + 1 == v => *h = v,
            _ => out.push((v, v)),
        }
    }
    out
}

impl From<&Inst> for System {
    fn from(inst: &Inst) -> Self {
        System {
            domains: (0..inst.len())
                .map(|i| {
                    let (lo, hi) = inst.range[i];
                    domain((lo..=hi).filter(|v| !inst.out[i].contains(v)))
                })
                .collect(),
            edges: inst.edges.clone(),
        }
    }
}

/// A component with more than one internal successor or predecessor of some name: refused.
#[derive(Debug, PartialEq, Eq)]
struct Unsupported;

/// One piece of a cycle's map from the first name's value to the value the cycle returns.
#[derive(Clone, Copy, Debug)]
struct Piece {
    lo: i64,
    hi: i64,
    value: i64,
    rising: bool,
}

impl Piece {
    fn end(self) -> i64 {
        self.value + if self.rising { self.hi - self.lo } else { 0 }
    }
}

/// The map as pieces keyed by output: outputs are monotone in the input.
struct Map {
    pieces: BTreeMap<(i64, i64), Piece>,
    shift: i64,
}

impl Map {
    fn insert(&mut self, piece: Piece) {
        self.pieces.insert((piece.value, piece.lo), piece);
    }

    /// Replaces the preimage of the outputs `a..=b` by a flat piece at `value`, or deletes it.
    fn edit(&mut self, a: i64, b: i64, value: Option<i64>) {
        let (a, b) = (a - self.shift, b - self.shift);
        let prior = self
            .pieces
            .range(..(a, i64::MIN))
            .next_back()
            .filter(|(_, p)| p.end() >= a)
            .map(|(k, _)| *k);
        let keys: Vec<(i64, i64)> = prior
            .into_iter()
            .chain(
                self.pieces
                    .range((Included((a, i64::MIN)), Unbounded))
                    .take_while(|(_, p)| p.value <= b)
                    .map(|(k, _)| *k),
            )
            .collect();
        let mut extent: Option<(i64, i64)> = None;
        for key in keys {
            let p = self.pieces.remove(&key).expect("a key of this map");
            let (l, h) = if p.rising {
                (p.lo.max(p.lo + a - p.value), p.hi.min(p.lo + b - p.value))
            } else {
                (p.lo, p.hi)
            };
            assert!(l <= h);
            extent = Some(extent.map_or((l, h), |(x, y)| (x.min(l), y.max(h))));
            if p.lo < l {
                self.insert(Piece { hi: l - 1, ..p });
            }
            if h < p.hi {
                self.insert(Piece {
                    lo: h + 1,
                    value: p.value + h + 1 - p.lo,
                    ..p
                });
            }
        }
        if let (Some((lo, hi)), Some(value)) = (extent, value) {
            self.insert(Piece {
                lo,
                hi,
                value: value - self.shift,
                rising: false,
            });
        }
    }

    /// Follows the map by the edge of weight `weight` into a name with `domain`, each output
    /// snapped down to a value of `domain`.
    fn compose(&mut self, domain: &Domain, weight: i64) {
        self.shift += weight;
        let (Some(&(lo, _)), Some(&(_, hi))) = (domain.first(), domain.last()) else {
            self.pieces.clear();
            return;
        };
        if let Some((_, p)) = self.pieces.first_key_value() {
            let first = p.value + self.shift;
            if first < lo {
                self.edit(first, lo - 1, None);
            }
        }
        if let Some((_, p)) = self.pieces.last_key_value() {
            let last = p.end() + self.shift;
            if last > hi {
                self.edit(hi + 1, last, Some(hi));
            }
        }
        for pair in domain.windows(2) {
            self.edit(pair[0].1 + 1, pair[1].0 - 1, Some(pair[0].1));
        }
    }
}

/// The greatest value of `domain` at most `cap`.
fn predecessor(domain: &Domain, cap: i64) -> Option<i64> {
    let i = domain.partition_point(|&(lo, _)| lo <= cap);
    (i > 0).then(|| domain[i - 1].1.min(cap))
}

fn composed_cycle(domains: &[&Domain], weights: &[i64]) -> Option<Map> {
    let first = domains[0];
    if first.is_empty() || weights.iter().sum::<i64>() < 0 {
        return None;
    }
    let mut map = Map {
        pieces: BTreeMap::new(),
        shift: 0,
    };
    map.insert(Piece {
        lo: first[0].0,
        hi: first.last().expect("a value").1,
        value: first[0].0,
        rising: true,
    });
    for i in 0..domains.len() {
        map.compose(domains[(i + 1) % domains.len()], weights[i]);
    }
    Some(map)
}

/// The exact values of the first name of a cycle; `weights[i]` enters name `i + 1` (mod n).
fn cycle_marginal(domains: &[Domain], weights: &[i64]) -> Domain {
    let refs: Vec<&Domain> = domains.iter().collect();
    let Some(map) = composed_cycle(&refs, weights) else {
        return vec![];
    };
    let mut result: Domain = vec![];
    let mut at = 0;
    for p in map.pieces.values() {
        let hi = if p.rising {
            if p.value + map.shift < p.lo {
                continue;
            }
            p.hi
        } else {
            p.hi.min(p.value + map.shift)
        };
        if hi < p.lo {
            continue;
        }
        while at < domains[0].len() && domains[0][at].1 < p.lo {
            at += 1;
        }
        while at < domains[0].len() && domains[0][at].0 <= hi {
            let (l, h) = domains[0][at];
            let (lo, end) = (l.max(p.lo), h.min(hi));
            match result.last_mut() {
                Some(last) if last.1 + 1 >= lo => last.1 = end,
                _ => result.push((lo, end)),
            }
            if h > hi {
                break;
            }
            at += 1;
        }
    }
    result
}

/// The greatest solution of a cycle in its order.
fn cycle(domains: &[&Domain], weights: &[i64]) -> Option<Vec<i64>> {
    let map = composed_cycle(domains, weights)?;
    let best = map.pieces.values().rev().find_map(|p| {
        let t = if p.rising {
            (p.value + map.shift >= p.lo).then_some(p.hi)
        } else {
            Some(p.hi.min(p.value + map.shift))
        };
        t.and_then(|t| predecessor(domains[0], t))
            .filter(|t| *t >= p.lo)
    })?;
    let mut out = vec![best];
    for i in 1..domains.len() {
        out.push(predecessor(domains[i], out[i - 1] + weights[i - 1])?);
    }
    Some(out)
}

/// The exact greatest solution, `None` when there is none, or the refusal by shape.
fn greatest(sys: &System) -> Result<Option<Vec<i64>>, Unsupported> {
    let n = sys.domains.len();
    let mut edges = BTreeMap::new();
    for &(u, v, w) in &sys.edges {
        edges
            .entry((u, v))
            .and_modify(|x: &mut i64| *x = (*x).min(w))
            .or_insert(w);
    }
    let mut out = vec![vec![]; n];
    let mut back = vec![vec![]; n];
    for (&(u, v), &w) in &edges {
        out[u].push((v, w));
        back[v].push(u);
    }
    // Kosaraju with explicit stacks: each name and edge visited once per pass.
    let mut visited = vec![false; n];
    let mut order = vec![];
    for root in 0..n {
        if visited[root] {
            continue;
        }
        visited[root] = true;
        let mut stack = vec![(root, 0)];
        while let Some((v, i)) = stack.last_mut() {
            if *i == out[*v].len() {
                order.push(*v);
                stack.pop();
            } else {
                let z = out[*v][*i].0;
                *i += 1;
                if !visited[z] {
                    visited[z] = true;
                    stack.push((z, 0));
                }
            }
        }
    }
    let mut comp = vec![usize::MAX; n];
    let mut groups: Vec<Vec<usize>> = vec![];
    for root in order.into_iter().rev() {
        if comp[root] != usize::MAX {
            continue;
        }
        let id = groups.len();
        let mut group = vec![];
        comp[root] = id;
        let mut stack = vec![root];
        while let Some(v) = stack.pop() {
            group.push(v);
            for &z in &back[v] {
                if comp[z] == usize::MAX {
                    comp[z] = id;
                    stack.push(z);
                }
            }
        }
        groups.push(group);
    }
    let mut internal = vec![vec![]; n];
    let mut inside_in = vec![0; n];
    let mut incoming = vec![0; groups.len()];
    for (&(u, v), &w) in &edges {
        if comp[u] == comp[v] {
            internal[u].push((v, w));
            inside_in[v] += 1;
        } else {
            incoming[comp[v]] += 1;
        }
    }
    // The shape is checked before any answer, so an inconsistent system is refused too.
    if groups.iter().any(|g| {
        g.len() > 1
            && g.iter()
                .any(|&v| internal[v].len() != 1 || inside_in[v] != 1)
    }) {
        return Err(Unsupported);
    }
    if sys.domains.iter().any(Vec::is_empty) {
        return Ok(None);
    }
    let mut cap: Vec<i64> = sys
        .domains
        .iter()
        .map(|d| d.last().expect("a value").1)
        .collect();
    let mut solution = vec![0; n];
    let mut queue: VecDeque<usize> = (0..groups.len()).filter(|&c| incoming[c] == 0).collect();
    while let Some(c) = queue.pop_front() {
        let group = &groups[c];
        if let [v] = group[..] {
            if internal[v].iter().any(|&(_, w)| w < 0) {
                return Ok(None);
            }
            let Some(t) = predecessor(&sys.domains[v], cap[v]) else {
                return Ok(None);
            };
            solution[v] = t;
        } else {
            let start = group[0];
            let (mut ids, mut weights, mut v) = (vec![], vec![], start);
            loop {
                ids.push(v);
                let (z, w) = internal[v][0];
                weights.push(w);
                v = z;
                if v == start {
                    break;
                }
            }
            let domains: Vec<Domain> = ids
                .iter()
                .map(|&v| {
                    sys.domains[v]
                        .iter()
                        .filter(|&&(l, _)| l <= cap[v])
                        .map(|&(l, h)| (l, h.min(cap[v])))
                        .collect()
                })
                .collect();
            let refs: Vec<&Domain> = domains.iter().collect();
            let Some(values) = cycle(&refs, &weights) else {
                return Ok(None);
            };
            for (&v, t) in ids.iter().zip(values) {
                solution[v] = t;
            }
        }
        for &v in group {
            for &(z, w) in &out[v] {
                if comp[z] != c {
                    cap[z] = cap[z].min(solution[v] + w);
                    incoming[comp[z]] -= 1;
                    if incoming[comp[z]] == 0 {
                        queue.push_back(comp[z]);
                    }
                }
            }
        }
    }
    Ok(Some(solution))
}

/// Every edge reversed and every domain negated: its greatest solution is the least of
/// `sys`, negated.
fn negated(sys: &System) -> System {
    System {
        domains: sys
            .domains
            .iter()
            .map(|d| d.iter().rev().map(|&(l, h)| (-h, -l)).collect())
            .collect(),
        edges: sys.edges.iter().map(|&(u, v, w)| (v, u, w)).collect(),
    }
}

/// The least solution, by [`greatest`] on [`negated`].
fn least(sys: &System) -> Result<Option<Vec<i64>>, Unsupported> {
    Ok(greatest(&negated(sys))?.map(|p| p.into_iter().map(|v| -v).collect()))
}

/// Each name's domain as one run from its least to its greatest value.
fn hull(sys: &System) -> System {
    System {
        domains: sys
            .domains
            .iter()
            .map(|d| match (d.first(), d.last()) {
                (Some(l), Some(h)) => vec![(l.0, h.1)],
                _ => vec![],
            })
            .collect(),
        edges: sys.edges.clone(),
    }
}

/// What enumeration of every point finds.
struct Oracle {
    upper: Option<Vec<i64>>,
    lower: Option<Vec<i64>>,
    projection: Vec<Domain>,
}

fn brute(sys: &System) -> Oracle {
    let n = sys.domains.len();
    let values: Vec<Vec<i64>> = sys
        .domains
        .iter()
        .map(|d| d.iter().flat_map(|&(l, h)| l..=h).collect())
        .collect();
    let mut seen: Vec<std::collections::BTreeSet<i64>> = vec![Default::default(); n];
    if values.iter().all(|v| !v.is_empty()) {
        let mut at = vec![0; n];
        loop {
            let x: Vec<i64> = (0..n).map(|i| values[i][at[i]]).collect();
            if sys.edges.iter().all(|&(u, v, w)| x[v] <= x[u] + w) {
                for (s, &t) in seen.iter_mut().zip(&x) {
                    s.insert(t);
                }
            }
            let mut k = 0;
            while k < n && at[k] + 1 == values[k].len() {
                at[k] = 0;
                k += 1;
            }
            if k == n {
                break;
            }
            at[k] += 1;
        }
    }
    let any = seen.iter().all(|s| !s.is_empty());
    Oracle {
        upper: any.then(|| seen.iter().map(|s| *s.last().expect("a value")).collect()),
        lower: any.then(|| seen.iter().map(|s| *s.first().expect("a value")).collect()),
        projection: seen.into_iter().map(domain).collect(),
    }
}

/// The named systems of the sources, as [`Inst`]s in `super::holes` are.
fn named() -> Vec<(&'static str, System)> {
    let s = |domains: Vec<Domain>, edges: Vec<(usize, usize, i64)>| System { domains, edges };
    vec![
        (
            "HeapInvariant",
            s(
                vec![
                    vec![(0, 0), (2, 4), (6, 7)],
                    vec![(1, 3), (5, 7)],
                    vec![(3, 6)],
                    vec![(0, 3), (6, 7)],
                ],
                vec![(0, 1, 3), (1, 2, -1), (2, 3, -1), (3, 0, 1)],
            ),
        ),
        (
            "CE-A",
            s(
                vec![vec![(4, 6)], vec![(4, 4), (6, 6)], vec![(2, 2), (4, 4)]],
                vec![(1, 2, -2), (2, 0, 2), (0, 1, 0)],
            ),
        ),
        (
            "CE-B",
            s(
                vec![vec![(3, 5)], vec![(5, 5), (7, 7)], vec![(6, 6), (8, 8)]],
                vec![(2, 1, 0), (0, 2, 3), (1, 0, -2)],
            ),
        ),
        (
            "collective",
            s(
                vec![vec![(0, 4), (6, 6)], vec![(0, 3), (5, 6)], vec![(0, 6)]],
                vec![(1, 2, 0), (0, 1, 0), (2, 0, 1)],
            ),
        ),
    ]
}

/// Codex round 4's families: laps (a cycle of weight 1, name 0 a multiple of 3 and name
/// `n/2` one more than a multiple of 3, in `0..=6n`), mixed (laps with one hole on every
/// other name) and the staircase (a cycle of weight 0, name `i` without `2n - i`).
fn family(name: &str, n: usize) -> System {
    let r = 6 * n as i64;
    let mut domains = vec![vec![(0, r)]; n];
    if name == "staircase" {
        for (i, d) in domains.iter_mut().enumerate() {
            let h = 2 * n as i64 - i as i64;
            *d = vec![(0, h - 1)];
            if h < 2 * n as i64 {
                d.push((h + 1, 2 * n as i64));
            }
        }
    } else {
        domains[0] = domain((0..=r).filter(|v| v % 3 == 0));
        domains[n / 2] = domain((0..=r).filter(|v| *v == 0 || v % 3 == 1));
        if name == "mixed" {
            for (i, d) in domains.iter_mut().enumerate().skip(1) {
                if i != n / 2 {
                    let h = r - i as i64;
                    *d = vec![(0, h - 1), (h + 1, r)];
                }
            }
        }
    }
    let mut edges: Vec<(usize, usize, i64)> = (0..n - 1).map(|i| (i, i + 1, 0)).collect();
    edges.push((n - 1, 0, i64::from(name != "staircase")));
    System { domains, edges }
}

/// Codex round 4's corpus, 4 modes of 5,000 systems each (seed `0x139`): cycles,
/// DAGs, random graphs, and two 2-cycles joined by one edge; 1 to 5 names in `-2..=3`.
fn corpus() -> Vec<(&'static str, System)> {
    let mut rng = Lcg(0x139);
    let mut all = named();
    for name in ["laps", "staircase", "mixed"] {
        for n in 2..=4 {
            all.push((name, family(name, n)));
        }
    }
    for mode in 0..4 {
        for _ in 0..5000 {
            let n = if mode == 3 {
                4
            } else {
                1 + rng.next(5) as usize
            };
            let domains = (0..n)
                .map(|_| domain((-2..=3).filter(|_| rng.next(4) > 0)))
                .collect();
            let w = |rng: &mut Lcg| rng.next(7) as i64 - 3;
            let edges = match mode {
                0 => (0..n).map(|i| (i, (i + 1) % n, w(&mut rng))).collect(),
                1 => (0..n)
                    .flat_map(|i| (i + 1..n).map(move |j| (i, j)))
                    .collect::<Vec<_>>()
                    .into_iter()
                    .filter_map(|(i, j)| {
                        if rng.next(3) == 0 {
                            Some((i, j, w(&mut rng)))
                        } else {
                            None
                        }
                    })
                    .collect(),
                3 => [(0, 1), (1, 0), (2, 3), (3, 2), (1, 2)]
                    .into_iter()
                    .map(|(u, v)| (u, v, w(&mut rng)))
                    .collect(),
                _ => (0..2 * n)
                    .map(|_| {
                        let u = rng.next(n as u64) as usize;
                        let v = rng.next(n as u64) as usize;
                        (u, v, w(&mut rng))
                    })
                    .collect(),
            };
            all.push((
                if mode == 0 { "cycle" } else { "random" },
                System { domains, edges },
            ));
        }
    }
    all
}

/// Codex round 4 (`work/r4/src/main.rs`, `check`): on every system of the corpus the model
/// gives the same answer with the names numbered backward, and on every system it accepts its
/// greatest and least solutions are those of enumeration; on the named systems and the
/// families, the set of each name (each value fixed in turn) is that of enumeration, and on
/// cycles [`cycle_marginal`] is each name's set. CONTROL: the model on each name's hull gives
/// a wrong greatest solution on some system, and the corpus has refused systems.
#[test]
fn scc_composition_matches_enumeration() {
    let (mut accepted, mut refused, mut hull_caught) = (0, 0, 0);
    for (name, sys) in &corpus() {
        let n = sys.domains.len();
        let got = greatest(sys);
        let backward = System {
            domains: sys.domains.iter().rev().cloned().collect(),
            edges: sys
                .edges
                .iter()
                .rev()
                .map(|&(u, v, w)| (n - 1 - u, n - 1 - v, w))
                .collect(),
        };
        let other = greatest(&backward).map(|p| {
            p.map(|mut p| {
                p.reverse();
                p
            })
        });
        assert_eq!(got, other, "names numbered backward: {sys:?}");
        let Ok(got) = got else {
            refused += 1;
            continue;
        };
        accepted += 1;
        let oracle = brute(sys);
        assert_eq!(got, oracle.upper, "greatest, {name}: {sys:?}");
        assert_eq!(
            least(sys).expect("the same shape"),
            oracle.lower,
            "least, {name}: {sys:?}"
        );
        if *name == "cycle" {
            for root in 0..n {
                let domains: Vec<Domain> = sys
                    .domains
                    .iter()
                    .cycle()
                    .skip(root)
                    .take(n)
                    .cloned()
                    .collect();
                let weights: Vec<i64> = sys
                    .edges
                    .iter()
                    .cycle()
                    .skip(root)
                    .take(n)
                    .map(|e| e.2)
                    .collect();
                assert_eq!(
                    cycle_marginal(&domains, &weights),
                    oracle.projection[root],
                    "cycle_marginal, root {root}: {sys:?}"
                );
            }
        }
        hull_caught += usize::from(greatest(&hull(sys)).expect("the same shape") != oracle.upper);
        if *name != "random" && *name != "cycle" {
            let sets: Vec<Domain> = (0..n)
                .map(|i| {
                    domain(
                        sys.domains[i]
                            .iter()
                            .flat_map(|&(l, h)| l..=h)
                            .filter(|&t| {
                                let mut fixed = sys.clone();
                                fixed.domains[i] = vec![(t, t)];
                                greatest(&fixed).expect("the same shape").is_some()
                            }),
                    )
                })
                .collect();
            assert_eq!(sets, oracle.projection, "sets, {name}");
        }
    }
    if let Some((_, heap)) = named().first() {
        assert_eq!(brute(heap).upper, Some(vec![4, 7, 6, 3]), "HeapInvariant");
    }
    assert!(accepted > 1000, "{accepted} accepted");
    assert!(refused > 0, "CONTROL: no system was refused");
    assert!(hull_caught > 0, "CONTROL: the hull was never wrong");
}

/// Codex round 4: a component that is not one cycle (a triangle with a chord) is refused by
/// its shape, also when a name has no value, so the refusal never depends on the numbers.
#[test]
fn scc_composition_refuses_a_component_that_is_not_one_cycle() {
    let bad = System {
        domains: vec![vec![(0, 3)]; 3],
        edges: vec![(0, 1, 0), (1, 2, 0), (2, 0, 0), (0, 2, 0)],
    };
    assert_eq!(greatest(&bad), Err(Unsupported));
    let mut empty = bad.clone();
    empty.domains[0].clear();
    assert_eq!(greatest(&empty), Err(Unsupported));
    // CONTROL: without the chord the triangle is one cycle and is answered.
    let mut cycle = bad;
    cycle.edges.pop();
    assert_eq!(greatest(&cycle), Ok(Some(vec![3, 3, 3])));
}

/// All-pairs shortest distances by Floyd–Warshall, `None` on a negative cycle.
fn distances(n: usize, edges: &[(usize, usize, i64)]) -> Option<Vec<Vec<Option<i64>>>> {
    let mut d = vec![vec![None; n]; n];
    for (i, row) in d.iter_mut().enumerate() {
        row[i] = Some(0);
    }
    for &(a, b, c) in edges {
        d[a][b] = Some(d[a][b].map_or(c, |x: i64| x.min(c)));
    }
    for k in 0..n {
        for i in 0..n {
            for j in 0..n {
                if let (Some(x), Some(y)) = (d[i][k], d[k][j]) {
                    d[i][j] = Some(d[i][j].map_or(x + y, |z| z.min(x + y)));
                }
            }
        }
    }
    (0..n).all(|i| d[i][i] == Some(0)).then_some(d)
}

/// How [`snapped`] treats holes.
#[derive(Clone, Copy, PartialEq)]
enum Snap {
    /// Snap each name to a value of its domain after every relaxation (the model).
    Always,
    /// CONTROL: never snap, so holes are ignored.
    Never,
    /// CONTROL (Gemini round 4): relax on the hull to its fixpoint, then snap each name once.
    Once,
}

/// The greatest solution by relaxing every name to `min_i u_i + d[i][j]` and snapping it
/// down to its domain until nothing changes (Codex round 3, `greatest`), name `cap.0` at most
/// `cap.1`.
fn snapped(sys: &System, cap: Option<(usize, i64)>, snap: Snap) -> Option<Vec<i64>> {
    let d = distances(sys.domains.len(), &sys.edges)?;
    if sys.domains.iter().any(Vec::is_empty) {
        return None;
    }
    let mut u: Vec<i64> = sys
        .domains
        .iter()
        .map(|s| s.last().expect("a value").1)
        .collect();
    if let Some((v, c)) = cap {
        u[v] = u[v].min(c);
    }
    let down = |u: &[i64]| -> Option<Vec<i64>> {
        u.iter()
            .zip(&sys.domains)
            .map(|(&x, dom)| predecessor(dom, x))
            .collect()
    };
    loop {
        let raw: Vec<i64> = (0..u.len())
            .map(|j| {
                (0..u.len())
                    .filter_map(|i| Some(u[i] + d[i][j]?))
                    .min()
                    .expect("d[j][j] = 0")
            })
            .collect();
        let next = if snap == Snap::Always {
            down(&raw)?
        } else {
            raw
        };
        if next == u {
            return if snap == Snap::Once {
                down(&u)
            } else {
                Some(u)
            };
        }
        u = next;
    }
}

/// Each name's set by repeated capped queries (Codex round 3, `projections`): the greatest
/// solution with name `v` below the cap gives a run of `v`'s values, and the cap moves below
/// that run.
fn projections(sys: &System) -> Vec<Domain> {
    let n = sys.domains.len();
    let Some(d) = distances(n, &sys.edges) else {
        return vec![vec![]; n];
    };
    (0..n)
        .map(|v| {
            let mut runs: Domain = vec![];
            let mut cap = i64::MAX;
            while let Some(u) = snapped(sys, Some((v, cap)), Snap::Always) {
                let lo = (0..n)
                    .filter_map(|i| {
                        let l = sys.domains[i]
                            .iter()
                            .find(|&&(l, h)| l <= u[i] && u[i] <= h)
                            .expect("a snapped value")
                            .0;
                        Some(l - d[v][i]?)
                    })
                    .max()
                    .expect("d[v][v] = 0");
                assert!(lo <= u[v]);
                runs.push((lo, u[v]));
                cap = lo - 1;
            }
            runs.reverse();
            let mut merged: Domain = vec![];
            for (l, h) in runs {
                match merged.last_mut() {
                    Some(m) if l <= m.1 + 1 => m.1 = m.1.max(h),
                    _ => merged.push((l, h)),
                }
            }
            merged
        })
        .collect()
}

/// Codex round 3 (`holes.mjs`, 6,000 random systems of 2 to 4 names in `0..=6`,
/// seed 235711) and the three named systems: the sets by capped queries, and the greatest and
/// least solutions by snapping, are those of enumeration. The sets of `super::holes`'s
/// equality chain at `n = 2..8` are the even numbers.
#[test]
fn closure_and_snapping_match_enumeration() {
    let mut rng = Lcg(235_711);
    let mut all: Vec<System> = named().into_iter().skip(1).map(|(_, s)| s).collect();
    for _ in 0..6000 {
        let n = 2 + rng.next(3) as usize;
        let domains = (0..n)
            .map(|_| domain((0..7).filter(|_| rng.next(3) != 0)))
            .collect();
        let edges = (0..rng.next(2 * n as u64 + 1))
            .map(|_| {
                let u = rng.next(n as u64) as usize;
                let v = rng.next(n as u64) as usize;
                (u, v, rng.next(7) as i64 - 3)
            })
            .collect();
        all.push(System { domains, edges });
    }
    for sys in &all {
        let oracle = brute(sys);
        assert_eq!(projections(sys), oracle.projection, "{sys:?}");
        assert_eq!(snapped(sys, None, Snap::Always), oracle.upper, "{sys:?}");
        let low = snapped(&negated(sys), None, Snap::Always)
            .map(|p| p.into_iter().map(|v| -v).collect::<Vec<_>>());
        assert_eq!(low, oracle.lower, "{sys:?}");
    }
    for n in 2..=8 {
        let sys = System {
            domains: (0..n as i64)
                .map(|i| vec![(0, 2 * i), (2 * i + 2, 2 * n as i64)])
                .collect(),
            edges: (0..n - 1)
                .flat_map(|i| [(i, i + 1, 0), (i + 1, i, 0)])
                .collect(),
        };
        let evens: Domain = (0..=n as i64).map(|i| (2 * i, 2 * i)).collect();
        assert_eq!(projections(&sys), vec![evens; n], "equality chain, n = {n}");
    }
}

/// The negative controls of the sources, each a wrong method that fails on a named case:
/// - hull (Codex round 3): sets computed on each name's hull are wrong on CE-B and the
///   collective example;
/// - no snapping (Codex round 3): `x0` in `{0, 2}`, `x1` in `0..=1`, `x0 = x1`: the greatest
///   solution is `(0, 0)`, relaxing without snapping gives `(1, 1)`;
/// - negative cycle (Codex round 3): `x1 <= x0 - 1`, `x0 <= x1` has no distances;
/// - snapping once after the hull's fixpoint (Gemini round 4, `snap_once_gfp`): a wrong
///   greatest solution on the staircase and the mixed family of 4 (on CE-A, CE-B and the
///   collective example it happens to be right, as Gemini's log shows);
/// - ends only (Gemini round 4, `proj_endpoints_only`): the values between the least and the
///   greatest solution keep `a = 5` in CE-A, `a = 4` in CE-B and `z = 4` in the collective
///   example.
#[test]
fn wrong_methods_fail_on_named_cases() {
    let named: BTreeMap<&str, System> = named().into_iter().collect();
    for name in ["CE-B", "collective"] {
        let sys = &named[name];
        assert_ne!(
            projections(&hull(sys)),
            brute(sys).projection,
            "hull, {name}"
        );
    }
    let hole = System {
        domains: vec![vec![(0, 0), (2, 2)], vec![(0, 1)]],
        edges: vec![(1, 0, 0), (0, 1, 0)],
    };
    assert_eq!(snapped(&hole, None, Snap::Always), Some(vec![0, 0]));
    assert_eq!(snapped(&hole, None, Snap::Never), Some(vec![1, 1]));
    assert!(distances(2, &[(0, 1, -1), (1, 0, 0)]).is_none());
    for name in ["staircase", "mixed"] {
        let sys = family(name, 4);
        let exact = brute(&sys).upper;
        assert_eq!(snapped(&sys, None, Snap::Always), exact, "{name} of 4");
        assert_ne!(
            snapped(&sys, None, Snap::Once),
            exact,
            "snapping once, {name} of 4"
        );
    }
    for (name, i, v) in [("CE-A", 0, 5), ("CE-B", 0, 4), ("collective", 2, 4)] {
        let sys = &named[name];
        let oracle = brute(sys);
        let (lo, hi) = (
            oracle.lower.expect("a solution"),
            oracle.upper.expect("a solution"),
        );
        assert!(lo[i] <= v && v <= hi[i], "ends only keep {v}, {name}");
        assert!(
            sys.domains[i].iter().any(|&(l, h)| l <= v && v <= h),
            "{v} is in the domain, {name}"
        );
        assert!(
            !oracle.projection[i].iter().any(|&(l, h)| l <= v && v <= h),
            "the exact set has no {v}, {name}"
        );
    }
}

mod bench;
