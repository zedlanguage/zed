//! 14 single-linkage clustering to k clusters: the closest pair of points in different clusters,
//! ties broken by (distance², smaller label, larger label) in natural tuple order; the larger
//! label is renamed to the smaller. n - k merges (none if k >= n). A cluster goes by its label,
//! which is therefore its least point.
//!
//! The merges come in rising distance, a level of equal distances at a time. Before the merges of
//! distance d the clusters are the components of the pairs nearer than d, whatever happened
//! within the levels below. Two points p, q at distance d in different clusters during that
//! level have no other point in the closed disk on pq as diameter, since a point r there would be
//! nearer than d to both, or a copy of p or q; so pq is an edge of every Delaunay triangulation of
//! the distinct points. A triangulation and a chain through each set of equal points therefore
//! hold every pair a level can merge, O(n) edges in all. Within a level the key picks the least
//! label that has a pair at all and joins its nearest-labeled neighbor to it, until its connected
//! part of the level is one cluster; then the next least label. That is a search by least label,
//! which [`Level::merge`] runs on the level's edges. O(n log n).

mod delaunay;

use std::cmp::Reverse;
use std::collections::{BTreeMap, BinaryHeap};

use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};

use crate::zedrt::{at, parse_int};
use delaunay::Point;

/// The clusters, as a union–find by size with path halving; each root holds its cluster's label.
struct Clusters {
    parent: Vec<usize>,
    size: Vec<usize>,
    least: Vec<usize>,
}

impl Clusters {
    fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
            size: vec![1; n],
            least: (0..n).collect(),
        }
    }

    fn root(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]];
            x = self.parent[x];
        }
        x
    }

    fn label(&mut self, x: usize) -> usize {
        let r = self.root(x);
        self.least[r]
    }

    /// Joins the clusters of `a` and `b`, which differ.
    fn join(&mut self, a: usize, b: usize) {
        let (mut a, mut b) = (self.root(a), self.root(b));
        if self.size[a] < self.size[b] {
            std::mem::swap(&mut a, &mut b);
        }
        self.parent[b] = a;
        self.size[a] += self.size[b];
        self.least[a] = self.least[a].min(self.least[b]);
    }
}

/// The work space of one level, by the root of each cluster at its start, empty between levels.
struct Level {
    near: Vec<Vec<usize>>,
    seen: Vec<bool>,
}

impl Level {
    /// Makes the first of at most `left` merges of the level `pairs`, pairs of points at one
    /// distance, and returns how many it made: by least label, each joining the least label it
    /// has a pair with, as the key orders them.
    fn merge(&mut self, pairs: &[(BigInt, usize, usize)], left: usize, c: &mut Clusters) -> usize {
        let mut touched = Vec::new();
        for &(_, p, q) in pairs {
            let (a, b) = (c.root(p), c.root(q));
            if a == b {
                continue;
            }
            for (u, v) in [(a, b), (b, a)] {
                if self.near[u].is_empty() {
                    touched.push(u);
                }
                self.near[u].push(v);
            }
        }
        touched.sort_unstable_by_key(|&u| c.least[u]);
        let mut made = 0;
        'search: for &start in &touched {
            if self.seen[start] {
                continue;
            }
            self.seen[start] = true;
            let mut next = BinaryHeap::new();
            let mut reach = |u: usize, next: &mut BinaryHeap<_>, c: &Clusters| {
                for &v in &self.near[u] {
                    if !self.seen[v] {
                        self.seen[v] = true;
                        next.push(Reverse((c.least[v], v)));
                    }
                }
            };
            reach(start, &mut next, c);
            while let Some(Reverse((_, v))) = next.pop() {
                if made == left {
                    break 'search;
                }
                c.join(start, v);
                made += 1;
                reach(v, &mut next, c);
            }
        }
        for u in touched {
            self.near[u].clear();
            self.seen[u] = false;
        }
        made
    }
}

/// Makes the first `merges`, fewer than the number of points, in the order the key gives.
fn link(points: Vec<Point>, merges: usize, clusters: &mut Clusters) {
    let n = points.len();
    let mut order: Vec<(Point, usize)> = points.into_iter().zip(0..).collect();
    order.sort_unstable();
    let mut pairs = Vec::new();
    // The distinct points in (x, y) order, and the first index of each in the input.
    let (mut sites, mut first): (Vec<Point>, Vec<usize>) = (Vec::new(), Vec::new());
    let mut previous = 0;
    for (point, p) in order {
        if sites.last() == Some(&point) {
            pairs.push((BigInt::zero(), previous, p));
        } else {
            sites.push(point);
            first.push(p);
        }
        previous = p;
    }
    for (s, t) in delaunay::edges(&sites) {
        let (dx, dy) = (&sites[s].0 - &sites[t].0, &sites[s].1 - &sites[t].1);
        pairs.push((&dx * &dx + &dy * &dy, first[s], first[t]));
    }
    pairs.sort_by(|x, y| x.0.cmp(&y.0));
    let mut level = Level {
        near: vec![Vec::new(); n],
        seen: vec![false; n],
    };
    let mut left = merges;
    for pairs in pairs.chunk_by(|x, y| x.0 == y.0) {
        if left == 0 {
            break;
        }
        left -= level.merge(pairs, left, clusters);
    }
}

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    let k = parse_int(at(lines, 0)?)?;
    let mut pts = Vec::new();
    for l in &lines[1..] {
        let point = l.split(' ').map(parse_int);
        pts.push(point.collect::<Result<Vec<BigInt>, String>>()?);
    }
    let n = pts.len();
    let mut clusters = Clusters::new(n);
    let merges = (BigInt::from(n) - k).max(BigInt::zero());
    if !merges.is_zero() {
        // Any merge reads the coordinates of every point, when there are two to pair.
        let mut points = Vec::with_capacity(n);
        if n >= 2 {
            for p in pts {
                at(&p, 1)?;
                let mut p = p.into_iter();
                let x = p
                    .next()
                    .expect("a first coordinate, since there is a second");
                points.push((x, p.next().expect("a second coordinate, checked")));
            }
        }
        let merges = merges.to_usize().filter(|&m| m < n);
        link(points, merges.ok_or("min() of no pairs")?, &mut clusters);
    }
    let mut by_label: BTreeMap<usize, Vec<String>> = BTreeMap::new();
    for i in 0..n {
        by_label
            .entry(clusters.label(i))
            .or_default()
            .push(i.to_string());
    }
    for (c, members) in by_label {
        say!(out, "{c}: {}", members.join(" "));
    }
    Ok(())
}
