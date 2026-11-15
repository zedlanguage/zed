use super::{components, on_cycle, tarjan};

/// A step of xorshift64, the random numbers of these tests.
fn next(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

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

fn random_graph(state: &mut u64) -> Vec<Vec<usize>> {
    let n = 1 + (next(state) % 12) as usize;
    let e = (next(state) % (3 * n as u64 + 1)) as usize;
    let mut edges = vec![Vec::new(); n];
    for _ in 0..e {
        let (u, v) = (next(state) as usize % n, next(state) as usize % n);
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
    let mut state = crate::seed::seed(
        "components_are_the_classes_of_mutual_reach_numbered_in_reverse_topological_order",
    );
    for _ in 0..5000 {
        components_agree(&random_graph(&mut state));
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
    let mut state = crate::seed::seed("a_node_is_on_a_cycle_exactly_when_it_reaches_itself");
    for _ in 0..5000 {
        cycles_agree(&random_graph(&mut state));
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
