//! Tests of [`Refine`] against Berkholz, Bonsma and Grohe's two claims for Algorithm 1 (module
//! comment): the partition is the coarsest stable one that refines the starting coloring, and
//! the colors are canonical, the same at corresponding vertices of isomorphic graphs.

use super::{Refine, refine_places};

/// splitmix64, a fixed stream so that each run tests the same graphs.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// A random digraph of `n` vertices, each arc present with probability `num / 8`, and a
/// surjective starting coloring with `k` colors.
fn graph(rng: &mut Rng) -> (Vec<usize>, usize, Vec<Vec<usize>>) {
    let n = 1 + rng.below(9);
    let k = 1 + rng.below(n.min(3));
    let num = rng.below(8) as u64;
    let color = (0..n)
        .map(|v| if v < k { v } else { rng.below(k) })
        .collect();
    let adj = (0..n)
        .map(|_| (0..n).filter(|_| rng.next() % 8 < num).collect())
        .collect();
    (color, k, adj)
}

/// The colors [`Refine`] gives, the arcs of `v` being `adj[v]`.
fn refined(color: &[usize], colors: usize, adj: &[Vec<usize>]) -> Vec<usize> {
    let mut start = vec![0];
    let mut arcs = Vec::new();
    for a in adj {
        arcs.extend_from_slice(a);
        start.push(arcs.len());
    }
    // No arc is listed twice, so a vertex has at most `n` arcs into one class.
    let mut r = Refine::new(color.to_vec(), colors, color.len());
    r.run(&start, &arcs);
    r.color
}

/// The naive refinement: in rounds, each vertex `w` takes the color of its old color and the
/// sorted colors of the vertices `v` with `w` in `adj[v]`, until no class splits. Its result
/// is the coarsest stable partition that refines the starting one.
fn naive(color: &[usize], adj: &[Vec<usize>]) -> Vec<usize> {
    let n = color.len();
    let mut color = color.to_vec();
    loop {
        let mut sig: Vec<(usize, Vec<usize>)> = (0..n).map(|w| (color[w], Vec::new())).collect();
        for (v, a) in adj.iter().enumerate() {
            for &w in a {
                sig[w].1.push(color[v]);
            }
        }
        for s in &mut sig {
            s.1.sort_unstable();
        }
        let mut sorted = sig.clone();
        sorted.sort();
        sorted.dedup();
        let next: Vec<usize> = sig
            .iter()
            .map(|s| sorted.binary_search(s).expect("a signature"))
            .collect();
        let before = {
            let mut c = color.clone();
            c.sort_unstable();
            c.dedup();
            c.len()
        };
        color = next;
        if sorted.len() == before {
            return color;
        }
    }
}

/// Whether `a` and `b` put the same pairs of vertices together.
fn same_partition(a: &[usize], b: &[usize]) -> bool {
    (0..a.len()).all(|i| (0..a.len()).all(|j| (a[i] == a[j]) == (b[i] == b[j])))
}

/// The coarsest stable partition, by comparison with [`naive`] on 3,000 random digraphs.
/// Red when the parts of a class that was waiting are not all pushed (lines 22-24 of the
/// paper's Algorithm 1): checked 2026-11-19 by changing `(waiting && k != c)` to `false` in
/// [`Refine::split`].
#[test]
fn refinement_is_the_coarsest_stable_partition() {
    let mut rng = Rng(1);
    for trial in 0..3000 {
        let (color, k, adj) = graph(&mut rng);
        let got = refined(&color, k, &adj);
        let want = naive(&color, &adj);
        assert!(
            same_partition(&got, &want),
            "trial {trial}: {color:?} {adj:?}: got {got:?}, want {want:?}"
        );
    }
}

/// Canonical colors: a copy of each graph with its vertices renumbered by a random permutation
/// `p` gets at `p[v]` the color the graph gets at `v`. Red when the classes that split are
/// handled in the order they were met rather than in increasing order (line 11 of the
/// paper's Algorithm 1): checked 2026-11-19 by deleting `splits.sort_unstable()` in
/// [`Refine::run`].
#[test]
fn refinement_colors_are_canonical() {
    let mut rng = Rng(2);
    for trial in 0..3000 {
        let (color, k, adj) = graph(&mut rng);
        let n = color.len();
        let mut p: Vec<usize> = (0..n).collect();
        for i in (1..n).rev() {
            p.swap(i, rng.below(i + 1));
        }
        let mut color2 = vec![0; n];
        let mut adj2 = vec![Vec::new(); n];
        for v in 0..n {
            color2[p[v]] = color[v];
            adj2[p[v]] = adj[v].iter().map(|&w| p[w]).collect();
        }
        let got = refined(&color, k, &adj);
        let got2 = refined(&color2, k, &adj2);
        for v in 0..n {
            assert_eq!(
                got[v], got2[p[v]],
                "trial {trial}: {color:?} {adj:?} under {p:?}"
            );
        }
    }
}

/// [`refine_places`] gives the coarsest stable partition of its graph of nodes and places, by
/// comparison with [`naive`] on 3,000 random graphs, in which a node may hold itself, a node
/// twice, or a node of no place, and the places of one node may share a color, as a meet's do.
/// Red when a place's arc to its node is dropped (checked 2026-11-22 by deleting
/// `adj[cursor[v + e]] = u` in `refine_places`), and when the degree bound counts only the arcs
/// out of a vertex (checked by mapping each vertex to `start[x + 1] - start[x]` alone: `Refine`
/// then indexes past its tally on a node whose places all share a color).
#[test]
fn refinement_of_nodes_and_places_is_the_coarsest_stable_partition() {
    let mut rng = Rng(3);
    for trial in 0..3000 {
        let v = 1 + rng.below(7);
        let places: Vec<(usize, usize)> = (0..rng.below(12))
            .map(|_| (rng.below(v), rng.below(v)))
            .collect();
        let size = v + places.len();
        let node_colors = 1 + rng.below(v.min(3));
        let place_colors = 1 + rng.below(3);
        let mut color: Vec<usize> = (0..v)
            .map(|x| {
                if x < node_colors {
                    x
                } else {
                    rng.below(node_colors)
                }
            })
            .collect();
        color.extend((0..places.len()).map(|_| node_colors + rng.below(place_colors)));
        // The colors are numbered so that every one below the count has a vertex.
        let mut used: Vec<usize> = color.clone();
        used.sort_unstable();
        used.dedup();
        let color: Vec<usize> = color
            .iter()
            .map(|c| used.binary_search(c).expect("a color"))
            .collect();
        // The arcs as `naive` reads them: `w` in `adj[x]` refines `w` by `x`, so a place is
        // refined by the child it holds and a node by its places.
        let mut adj = vec![Vec::new(); size];
        for (e, &(u, c)) in places.iter().enumerate() {
            adj[c].push(v + e);
            adj[v + e].push(u);
        }
        let got = refine_places(color.clone(), used.len(), v, places.iter().copied());
        let want = naive(&color, &adj);
        assert!(
            same_partition(&got, &want),
            "trial {trial}: {color:?} {places:?}: got {got:?}, want {want:?}"
        );
    }
}
