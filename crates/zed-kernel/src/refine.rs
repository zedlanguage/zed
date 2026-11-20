//! Canonical color refinement: the coarsest stable coloring of a graph, its colors numbered by
//! the structure alone. A coloring is stable when any two vertices of one color have, for every
//! color, as many neighbors of that color. A popped color class R refines every class by the
//! number of neighbors in R each of its vertices has. After a split, the largest new class is
//! not pushed unless the old one was waiting (Hopcroft's rule, "process the smaller half": J.
//! Hopcroft, "An n log n algorithm for minimizing states in a finite automaton", Theory of
//! Machines and Computations, Academic Press, 1971, pp. 189-196,
//! doi:10.1016/b978-0-12-417750-5.50022-1; Crossref, not read), so a
//! vertex is in O(log N) refining classes in all: O((N + M) log N) for N vertices and M arcs.
//! New colors are numbered in the increasing order of (old color, number of neighbors), never
//! by a hash, so two isomorphic graphs whose starting colors correspond get the same color at
//! corresponding vertices.
//!
//! Source. C. Berkholz, P. Bonsma and M. Grohe, "Tight lower and upper bounds for the complexity
//! of canonical colour refinement", Theory of Computing Systems 60(4), 581-614, 2017 (online
//! 2016), doi:10.1007/s00224-016-9686-0; arXiv:1509.08251. Section 3.2, Algorithm 1 ("A
//! canonical colour refinement algorithm"), is the algorithm here; Algorithms 2 and 3 are its
//! fast implementation and the subroutine SplitUpColour. Algorithm 1 in the paper's steps and
//! this module's code:
//! - lines 5-7: a stack Q holds the starting colors in increasing order; pop a refining color
//!   r (`Worklist::first(.., Order::Lifo)` and `waiting.pop` in [`Refine::run`]);
//! - line 9: cdeg(v) = |N+(v) ∩ C_r| for every vertex (`count`, filled from the arcs of `adj`);
//! - lines 10-11: the colors whose vertices differ in cdeg, "in increasing order" (`splits`,
//!   sorted);
//! - lines 16-17: the new colors are {s} ∪ {maxcol + 1, ...}, given to the values of cdeg in
//!   increasing order, so the least value keeps s (`Refine::split`, `i == least[c]`);
//! - lines 22-28: if s is on Q every new color is pushed; otherwise all but the color of
//!   "b := min{i | for all j: NumDeg(i) >= NumDeg(j)}", the least value among the largest
//!   classes (`big`, chosen with a strict `>` so that ties go to the least value).
//!
//! The bound is the arXiv version's Lemmas 3 and 4 and Theorem 5 (section 3.3): one iteration
//! costs O(|R| + D-(R) + k log k), and "every v in V(G) appears at most log2 n times in a
//! refining colour class", since a pushed class has at most half the vertices of the class it
//! split from, which gives O((n + m) log n) in all. The paper credits the halving to Hopcroft's DFA
//! minimization and the bound first to Cardon and Crochemore, then to Paige and Tarjan, "Three
//! partition refinement algorithms", SIAM J. Comput. 16(6), 973-989, 1987,
//! doi:10.1137/0216062, p. 982.
//!
//! Departures. Colors count from 0, not 1. The paper refines by out-neighbors N+(v); here the
//! caller gives the arcs to count (`adj`), so a directed graph refines by whichever side it
//! lists. Algorithm 2's sort of the new colors' cdeg values, O(k log k), is a count over
//! `0..=most[c]` here, O(max cdeg), which the arcs read in the same iteration already pay for.
//!
//! Checked 2026-11-19 against the arXiv LaTeX of 1509.08251 (creffull9_clean.tex lines 291-345
//! for Algorithm 1, 456-498 for the lemma and its proof, 165-171 for the credits); Crossref
//! metadata for both papers. Paige and Tarjan's text was not read: the bound and the page are
//! taken from Berkholz, Bonsma and Grohe's citation of it (line 165).
//!
//! Tested by `refine::tests`: the result is compared with the naive refinement by rounds on
//! random digraphs, which catches a refinement that stops early or splits too much, such as
//! one that drops the rule that pushes every part of a class that was waiting; and relabeled
//! copies of each graph must get the same color at corresponding vertices, which catches
//! colors numbered in an order that follows the vertices' numbers, such as splits handled in
//! the order they were met. Neither test measures the O((N + M) log N) time.
//!
//! The neighbors are given as arcs: popping class R counts, for each vertex `w` listed in
//! `adj` of a vertex of R, the arcs into R from `w`. An undirected graph lists each edge both
//! ways (`zedc-presburger`'s `stable_colors`); a directed one lists each vertex's predecessors,
//! which refines by successors (the canonical form of recursive type groups, `types::rec`).
//! Moved here from `zedc-presburger` (item REC-canon), since `zed-kernel` does not depend on it.

// Complexity tradeoff (COMPLEXITY.md K72): the naive refinement recolors every vertex by its
// neighbors' colors in rounds until no class splits, O(N + M) per round and up to N rounds,
// O(N (N + M)). Used: each popped class refines only the classes of its neighbors, and the
// largest part of a split is not pushed (Hopcroft's rule), O((N + M) log N). Given up: memory
// for the arrays by color and by vertex (`members`, `at`, `count`, the stack), all O(N), and a
// larger constant factor per step than one round of the naive version.

use std::mem;

use zed_graph::{Order, Worklist};

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
    /// The colors waiting to refine the others, last in first out.
    waiting: Worklist,
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
        Refine {
            color,
            members,
            at,
            colors,
            waiting: Worklist::first(size, colors, Order::Lifo),
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
        while let Some(r) = self.waiting.pop() {
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
        let waiting = self.waiting.is_queued(c);
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
            // k is never waiting here: a new color is not, and `c` is pushed only when it was
            // not, so the push always queues it, as the stack did.
            if (waiting && k != c) || (!waiting && i != big) {
                self.waiting.push(k);
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

#[cfg(test)]
mod tests;
