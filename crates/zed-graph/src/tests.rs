use std::collections::HashMap;

use super::{Search, Walk, components, on_cycle, tarjan};
use crate::seed::Rng;

/// Which nodes each node reaches by a path of one edge or more, by repeated search from each
/// node: O(n (n + e)), the plain method the tests check Tarjan's against.
fn reaches(edges: &[Vec<usize>]) -> Vec<Vec<bool>> {
    let n = edges.len();
    (0..n)
        .map(|s| {
            let mut seen = vec![false; n];
            let mut todo: Vec<usize> = edges[s].clone();
            while let Some(v) = todo.pop() {
                if !seen[v] {
                    seen[v] = true;
                    todo.extend(&edges[v]);
                }
            }
            seen
        })
        .collect()
}

fn random_graph(rng: &mut Rng) -> Vec<Vec<usize>> {
    let n = 1 + rng.below(12);
    let e = rng.below(3 * n + 1);
    let mut edges = vec![Vec::new(); n];
    for _ in 0..e {
        let (u, v) = (rng.below(n), rng.below(n));
        edges[u].push(v);
    }
    edges
}

/// Nodes 0 and 1 reach each other by `0 -> 1 -> 0`, so they are one component and both lie
/// on a cycle; node 2 has no edge, so it is a component of its own and on no cycle. The
/// built graph of the tests below that gives each outcome they check.
const BUILT: [&[usize]; 3] = [&[1], &[0], &[]];

/// Checks the components of `edges` against mutual reach; returns the pairs of distinct
/// nodes put in one component and those put apart.
fn components_agree(edges: &[Vec<usize>]) -> (usize, usize) {
    let (mut merged, mut split) = (0, 0);
    let n = edges.len();
    let comp = components(edges, |&w| w);
    let reach = reaches(edges);
    for u in 0..n {
        for v in 0..n {
            let same = u == v || (reach[u][v] && reach[v][u]);
            assert_eq!(comp[u] == comp[v], same, "{edges:?}: nodes {u} and {v}");
            if u != v {
                if same { merged += 1 } else { split += 1 }
            }
        }
        for &w in &edges[u] {
            assert!(comp[w] <= comp[u], "{edges:?}: edge {u} -> {w}");
        }
    }
    // The numbers are 0 up to the count of components, each used.
    let count = comp.iter().max().map_or(0, |&m| m + 1);
    let mut used = vec![false; count];
    for &c in &comp {
        used[c] = true;
    }
    assert!(used.iter().all(|&u| u), "{edges:?}: {comp:?}");
    (merged, split)
}

#[test]
fn components_are_the_classes_of_mutual_reach_numbered_in_reverse_topological_order() {
    // Both outcomes on the built graph, so the check could fail either way on every run.
    let built: Vec<Vec<usize>> = BUILT.iter().map(|e| e.to_vec()).collect();
    let (merged, split) = components_agree(&built);
    assert!(merged > 0, "{built:?}: no pair merged");
    assert!(split > 0, "{built:?}: no pair split");
    let (mut rng, _) = Rng::fresh(
        "components_are_the_classes_of_mutual_reach_numbered_in_reverse_topological_order",
    );
    for _ in 0..5000 {
        components_agree(&random_graph(&mut rng));
    }
}

/// Checks `on_cycle` on `edges` against reach; returns the nodes on a cycle and those not.
fn cycles_agree(edges: &[Vec<usize>]) -> (usize, usize) {
    let (mut yes, mut no) = (0, 0);
    let cyclic = on_cycle(edges);
    let reach = reaches(edges);
    for v in 0..edges.len() {
        assert_eq!(cyclic[v], reach[v][v], "{edges:?}: node {v}");
        if cyclic[v] { yes += 1 } else { no += 1 }
    }
    (yes, no)
}

#[test]
fn a_node_is_on_a_cycle_exactly_when_it_reaches_itself() {
    let built: Vec<Vec<usize>> = BUILT.iter().map(|e| e.to_vec()).collect();
    let (yes, no) = cycles_agree(&built);
    assert!(yes > 0, "{built:?}: no node on a cycle");
    assert!(no > 0, "{built:?}: every node on a cycle");
    let (mut rng, _) = Rng::fresh("a_node_is_on_a_cycle_exactly_when_it_reaches_itself");
    for _ in 0..5000 {
        cycles_agree(&random_graph(&mut rng));
    }
}

#[test]
fn a_self_loop_is_a_cycle_and_a_lone_node_is_not() {
    assert_eq!(on_cycle(&[vec![0], vec![]]), [true, false]);
    assert_eq!(on_cycle(&[vec![1], vec![0], vec![1]]), [true, true, false]);
}

#[test]
fn the_search_reads_only_what_the_roots_reach_and_skips_the_edges_left_out() {
    // 0 -> 1 -> 0 is a cycle only by the edge marked out; 2 is not reached from root 0.
    let edges: Vec<Vec<(usize, bool)>> = vec![vec![(1, true)], vec![(0, false)], vec![(0, true)]];
    let mut found = Vec::new();
    tarjan(
        3,
        [0],
        |v| &edges[v],
        |&(w, kept)| kept.then_some(w),
        |members| found.push(members.to_vec()),
    );
    assert_eq!(found, [vec![1], vec![0]]);
}

#[test]
fn members_come_in_the_order_the_search_reached_them() {
    // 0 -> 1 -> 2 -> 0: reached 0, 1, 2, so the component is given as [0, 1, 2].
    let edges = [vec![1], vec![2], vec![0]];
    let mut found = Vec::new();
    tarjan(
        3,
        0..3,
        |v| &edges[v],
        |&w| Some(w),
        |m| found.push(m.to_vec()),
    );
    assert_eq!(found, [vec![0, 1, 2]]);
}

#[test]
fn a_long_chain_needs_no_deep_stack() {
    // A recursive search would use one frame per node; 200,000 nodes of a cycle run here on
    // a 64 KiB thread stack.
    let n = 200_000;
    let edges: Vec<Vec<usize>> = (0..n).map(|v| vec![(v + 1) % n]).collect();
    let cyclic = std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(move || on_cycle(&edges))
        .unwrap()
        .join()
        .unwrap();
    assert!(cyclic.iter().all(|&c| c));
}

/// A graph whose nodes are labels, numbered by the walk as it meets them, as a caller with no
/// numbering of its own does; it records each component found, by labels, with the label it
/// was reached from, and the label of each node whose edges the search read.
struct Labeled<'g> {
    edges: &'g HashMap<u64, Vec<u64>>,
    number: HashMap<u64, usize>,
    label: Vec<u64>,
    found: Vec<(Vec<u64>, Option<u64>)>,
    read: Vec<u64>,
}

impl<'g> Labeled<'g> {
    fn new(edges: &'g HashMap<u64, Vec<u64>>) -> Self {
        Labeled {
            edges,
            number: HashMap::new(),
            label: Vec::new(),
            found: Vec::new(),
            read: Vec::new(),
        }
    }

    /// The number of `x`, given the first time `x` is met.
    fn number(&mut self, x: u64) -> usize {
        *self.number.entry(x).or_insert_with(|| {
            self.label.push(x);
            self.label.len() - 1
        })
    }
}

impl Walk for Labeled<'_> {
    type At = usize;

    fn next(&mut self, v: usize, k: &mut usize) -> Option<usize> {
        let x = self.label[v];
        if *k == 0 {
            self.read.push(x);
        }
        let w = *self.edges[&x].get(*k)?;
        *k += 1;
        Some(self.number(w))
    }

    fn found(&mut self, members: &mut [usize], from: Option<usize>) {
        let members = members.iter().map(|&m| self.label[m]).collect();
        self.found.push((members, from.map(|f| self.label[f])));
    }
}

/// The label of node `v` of a graph of the tests: spread out, so the numbers the walk gives
/// are not the nodes' own.
fn label(v: usize) -> u64 {
    (v as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0x5555
}

fn labeled(edges: &[Vec<usize>]) -> HashMap<u64, Vec<u64>> {
    (0..edges.len())
        .map(|v| (label(v), edges[v].iter().map(|&w| label(w)).collect()))
        .collect()
}

/// Checks the components a [`Search`] gives over `walk` against reach in `edges`, the
/// components of every run so far being in `walk.found`, and the nodes `roots` of each run in
/// `roots`: each node in one component, the members of one component exactly the nodes that
/// reach each other, every component after those it reaches, each node's edges read once, and
/// `from` the node an edge reached the first member by, `None` only for a root. Returns the
/// pairs of distinct nodes put in one component and those put apart.
fn lazy_agree(edges: &[Vec<usize>], walk: &Labeled, roots: &[usize]) -> (usize, usize) {
    let n = edges.len();
    let node: HashMap<u64, usize> = (0..n).map(|v| (label(v), v)).collect();
    let mut comp = vec![usize::MAX; n];
    for (c, (members, from)) in walk.found.iter().enumerate() {
        for x in members {
            assert_eq!(
                comp[node[x]],
                usize::MAX,
                "{edges:?}: node {} twice",
                node[x]
            );
            comp[node[x]] = c;
        }
        let first = node[&members[0]];
        match from {
            Some(f) => assert!(edges[node[f]].contains(&first), "{edges:?}: from {f}"),
            None => assert!(roots.contains(&first), "{edges:?}: {first} is no root"),
        }
    }
    let reach = reaches(edges);
    let mut reached = vec![false; n];
    for &r in roots {
        reached[r] = true;
        for w in 0..n {
            reached[w] |= reach[r][w];
        }
    }
    let mut read: Vec<usize> = walk.read.iter().map(|x| node[x]).collect();
    read.sort();
    let expected: Vec<usize> = (0..n).filter(|&v| reached[v]).collect();
    assert_eq!(read, expected, "{edges:?}: the nodes read");
    let (mut merged, mut split) = (0, 0);
    for u in (0..n).filter(|&u| reached[u]) {
        for v in (0..n).filter(|&v| reached[v]) {
            let same = u == v || (reach[u][v] && reach[v][u]);
            assert_eq!(comp[u] == comp[v], same, "{edges:?}: nodes {u} and {v}");
            if u != v {
                if same { merged += 1 } else { split += 1 }
            }
        }
        for &w in &edges[u] {
            assert!(comp[w] <= comp[u], "{edges:?}: edge {u} -> {w}");
        }
    }
    (merged, split)
}

#[test]
fn a_search_over_nodes_numbered_as_met_finds_the_classes_of_mutual_reach() {
    // Both outcomes on the built graph from root 0: 0 and 1 merged, 2 not reached; from both
    // roots, 2 apart from them.
    let built: Vec<Vec<usize>> = BUILT.iter().map(|e| e.to_vec()).collect();
    let map = labeled(&built);
    let mut walk = Labeled::new(&map);
    let roots = [walk.number(label(0))];
    Search::new().run(&mut walk, roots);
    assert_eq!(walk.found, [(vec![label(0), label(1)], None)]);
    assert_eq!(lazy_agree(&built, &walk, &[0]), (2, 0));
    let mut walk = Labeled::new(&map);
    let roots: Vec<usize> = [2, 0].iter().map(|&v| walk.number(label(v))).collect();
    Search::new().run(&mut walk, roots);
    let (merged, split) = lazy_agree(&built, &walk, &[2, 0]);
    assert!(merged > 0 && split > 0, "{built:?}");
    let (mut rng, _) =
        Rng::fresh("a_search_over_nodes_numbered_as_met_finds_the_classes_of_mutual_reach");
    for _ in 0..5000 {
        let edges = random_graph(&mut rng);
        let n = edges.len();
        // A random subset of the nodes as roots, in a random order, some twice.
        let roots: Vec<usize> = (0..1 + rng.below(n + 1)).map(|_| rng.below(n)).collect();
        let map = labeled(&edges);
        let mut walk = Labeled::new(&map);
        let numbers: Vec<usize> = roots.iter().map(|&r| walk.number(label(r))).collect();
        Search::new().run(&mut walk, numbers);
        lazy_agree(&edges, &walk, &roots);
    }
}

#[test]
fn a_search_run_again_after_its_graph_grows_reads_only_the_new_nodes() {
    let (mut rng, _) =
        Rng::fresh("a_search_run_again_after_its_graph_grows_reads_only_the_new_nodes");
    let (mut merged_new, mut split_new) = (0, 0);
    for _ in 0..5000 {
        // Old nodes 0..a with edges among themselves; new nodes a..n with edges to any node.
        let old = random_graph(&mut rng);
        let a = old.len();
        let n = a + 1 + rng.below(8);
        let mut edges = old;
        edges.resize(n, Vec::new());
        for _ in 0..rng.below(3 * (n - a) + 1) {
            let u = a + rng.below(n - a);
            edges[u].push(rng.below(n));
        }
        let map = labeled(&edges);
        let mut walk = Labeled::new(&map);
        let mut search = Search::new();
        let first: Vec<usize> = (0..a).map(|v| walk.number(label(v))).collect();
        search.run(&mut walk, first);
        let (found, read) = (walk.found.len(), walk.read.len());
        assert_eq!(read, a, "{edges:?}: the first run reads the old nodes only");
        let second: Vec<usize> = (a..n).rev().map(|v| walk.number(label(v))).collect();
        search.run(&mut walk, second);
        let is_new = |x: &u64| (a..n).any(|v| label(v) == *x);
        assert!(
            walk.read[read..].iter().all(is_new),
            "{edges:?}: the second run reads an old node"
        );
        for (members, _) in &walk.found[found..] {
            assert!(
                members.iter().all(is_new),
                "{edges:?}: an old node found again"
            );
            if members.len() > 1 {
                merged_new += 1;
            } else {
                split_new += 1;
            }
        }
        let all: Vec<usize> = (0..n).collect();
        lazy_agree(&edges, &walk, &all);
    }
    // Both outcomes among the new nodes: a component of several new nodes and one of one.
    assert!(merged_new > 0 && split_new > 0, "{merged_new} {split_new}");
}

#[test]
fn a_search_with_no_roots_finds_nothing_and_a_root_found_before_is_passed_over() {
    let edges = [vec![0], vec![0]];
    let map = labeled(&edges);
    let mut walk = Labeled::new(&map);
    let mut search = Search::new();
    search.run(&mut walk, []);
    assert!(walk.found.is_empty() && walk.read.is_empty());
    let r = walk.number(label(0));
    search.run(&mut walk, [r, r]);
    search.run(&mut walk, [r]);
    // 0 is found once, as a root, its self-loop read once.
    assert_eq!(walk.found, [(vec![label(0)], None)]);
    assert_eq!(walk.read, [label(0)]);
    let r = walk.number(label(1));
    search.run(&mut walk, [r]);
    assert_eq!(walk.found[1], (vec![label(1)], None));
    assert_eq!(walk.read, [label(0), label(1)]);
}
