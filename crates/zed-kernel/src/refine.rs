//! Canonical color refinement (Berkholz, Bonsma and Grohe, "Tight lower and upper bounds for
//! the complexity of canonical colour refinement", Theory Comput. Syst. 60, 2017; arXiv:1509.08251,
//! section 3, Algorithms 2 and 3): the coarsest stable coloring of a graph, its colors numbered
//! by the structure alone. A coloring is stable when any two vertices of one color have, for
//! every color, as many neighbors of that color. A popped color class R refines every class by
//! the number of neighbors in R each of its vertices has. After a split, the largest new class is
//! not pushed unless the old one was waiting (Hopcroft's rule, "process the smaller half"), so a
//! vertex is in O(log N) refining classes in all: O((N + M) log N) for N vertices and M arcs
//! (Paige and Tarjan, "Three partition refinement algorithms", SIAM J. Comput. 16(6), 1987,
//! end of section 3). New colors are numbered in the increasing order of (old color, number of
//! neighbors), never by a hash, so two isomorphic graphs whose starting colors correspond get
//! the same color at corresponding vertices.
//!
//! The neighbors are given as arcs: popping class R counts, for each vertex `w` listed in
//! `adj` of a vertex of R, the arcs into R from `w`. An undirected graph lists each edge both
//! ways (`zedc-presburger`'s `stable_colors`); a directed one lists each vertex's predecessors,
//! which refines by successors (the canonical form of recursive type groups, `types::rec`).
//! Moved here from `zedc-presburger` (item REC-canon), since `zed-kernel` does not depend on it.

use std::mem;

/// The state of a refinement, after Berkholz, Bonsma and Grohe's
/// Algorithms 2 and 3. Arrays by color have one entry for each vertex, the most colors there
/// can be.
pub struct Refine {
    /// The color of each vertex.
    pub color: Vec<usize>,
    /// The vertices of each color, in no particular order.
    members: Vec<Vec<usize>>,
    /// The place of each vertex in its color's `members`.
    at: Vec<usize>,
    /// How many colors there are.
    colors: usize,
    /// The colors waiting to refine the others, and whether each is waiting.
    stack: Vec<usize>,
    queued: Vec<bool>,
    /// For the class being refined by: each vertex's number of neighbors in it.
    count: Vec<usize>,
    /// For each color, its vertices with a neighbor in the class, the most and least of their
    /// numbers, and whether it is in `adjacent`.
    hit: Vec<Vec<usize>>,
    most: Vec<usize>,
    least: Vec<usize>,
    seen: Vec<bool>,
    /// The colors with a vertex next to the class, and those of them that split.
    adjacent: Vec<usize>,
    splits: Vec<usize>,
    /// By number of neighbors, for one split: how many vertices have it, and their new color.
    tally: Vec<usize>,
    new: Vec<usize>,
}

impl Refine {
    /// The refinement of the coloring `color`, with colors `0..colors`, of a graph whose
    /// vertices have at most `degree` neighbors.
    pub fn new(color: Vec<usize>, colors: usize, degree: usize) -> Refine {
        let size = color.len();
        let mut members = vec![Vec::new(); size];
        let mut at = vec![0; size];
        for (v, &c) in color.iter().enumerate() {
            at[v] = members[c].len();
            members[c].push(v);
        }
        let mut queued = vec![false; size];
        queued[..colors].fill(true);
        Refine {
            color,
            members,
            at,
            colors,
            stack: (0..colors).collect(),
            queued,
            count: vec![0; size],
            hit: vec![Vec::new(); size],
            most: vec![0; size],
            least: vec![0; size],
            seen: vec![false; size],
            adjacent: Vec::new(),
            splits: Vec::new(),
            tally: vec![0; degree + 1],
            new: vec![0; degree + 1],
        }
    }

    /// Refines until no waiting color splits another: the coloring is then stable. The vertices
    /// counted when the class of `v` refines are `adj[start[v]..start[v + 1]]`.
    pub fn run(&mut self, start: &[usize], adj: &[usize]) {
        while let Some(r) = self.stack.pop() {
            self.queued[r] = false;
            let Refine {
                color,
                members,
                count,
                hit,
                most,
                least,
                seen,
                adjacent,
                splits,
                ..
            } = self;
            for &v in &members[r] {
                for &w in &adj[start[v]..start[v + 1]] {
                    let c = color[w];
                    count[w] += 1;
                    if count[w] == 1 {
                        hit[c].push(w);
                    }
                    if !seen[c] {
                        seen[c] = true;
                        adjacent.push(c);
                    }
                    most[c] = most[c].max(count[w]);
                }
            }
            for &c in adjacent.iter() {
                least[c] = if hit[c].len() < members[c].len() {
                    0
                } else {
                    hit[c]
                        .iter()
                        .map(|&v| count[v])
                        .min()
                        .expect("a vertex hit")
                };
                if least[c] < most[c] {
                    splits.push(c);
                }
            }
            splits.sort_unstable();
            let mut splits = mem::take(&mut self.splits);
            for &c in &splits {
                self.split(c);
            }
            splits.clear();
            self.splits = splits;
            for &c in &self.adjacent {
                for &v in &self.hit[c] {
                    self.count[v] = 0;
                }
                self.hit[c].clear();
                self.most[c] = 0;
                self.seen[c] = false;
            }
            self.adjacent.clear();
        }
    }

    /// Splits color `c` by the numbers of neighbors its vertices have in the refining class.
    /// The vertices with the least number keep `c`; the others take new colors in increasing
    /// order of their number. Every new class waits to refine except the largest, unless `c`
    /// was waiting already, and then all do.
    fn split(&mut self, c: usize) {
        let top = self.most[c];
        let hit = mem::take(&mut self.hit[c]);
        self.tally[..=top].fill(0);
        self.tally[0] = self.members[c].len() - hit.len();
        for &v in &hit {
            self.tally[self.count[v]] += 1;
        }
        let mut big = 0;
        for i in 1..=top {
            if self.tally[i] > self.tally[big] {
                big = i;
            }
        }
        let waiting = self.queued[c];
        for i in 0..=top {
            if self.tally[i] == 0 {
                continue;
            }
            let k = if i == self.least[c] {
                c
            } else {
                self.colors += 1;
                self.colors - 1
            };
            self.new[i] = k;
            if (waiting && k != c) || (!waiting && i != big) {
                self.queued[k] = true;
                self.stack.push(k);
            }
        }
        for &v in &hit {
            let k = self.new[self.count[v]];
            if k != c {
                let place = self.at[v];
                self.members[c].swap_remove(place);
                if let Some(&u) = self.members[c].get(place) {
                    self.at[u] = place;
                }
                self.at[v] = self.members[k].len();
                self.members[k].push(v);
                self.color[v] = k;
            }
        }
        self.hit[c] = hit;
    }
}
