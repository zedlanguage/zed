//! The weak topological order against its declarative definition.
//!
//! The definition, written here without Bourdoncle's stack: run a depth-first search from
//! the roots in order, visiting successors in the order of their lists, and number the
//! vertices in preorder and in finish order. Group the vertices into strongly connected components by
//! mutual reachability; a component's head is its member with the least preorder number,
//! and the components are listed by decreasing finish time of their heads. A component with
//! one vertex and no self-loop is that vertex; any other is the head followed by the order
//! of the rest of the component, computed the same way with the edges into the head removed
//! and the head's successors as roots.

use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zedc::store::wto::{Element, ordered_by, show, weak_topological_order};

/// The declarative order of the vertices `within` (a subset of the graph), from `roots`.
fn declarative(succ: &[Vec<usize>], within: &[usize], roots: &[usize]) -> Vec<Element> {
    let inside = |v: usize| within.contains(&v);
    let n = succ.len();
    let (mut pre, mut fin) = (vec![usize::MAX; n], vec![usize::MAX; n]);
    let (mut p, mut f) = (0, 0);
    fn dfs(
        v: usize,
        succ: &[Vec<usize>],
        inside: &dyn Fn(usize) -> bool,
        pre: &mut [usize],
        fin: &mut [usize],
        p: &mut usize,
        f: &mut usize,
    ) {
        pre[v] = *p;
        *p += 1;
        for &w in &succ[v] {
            if inside(w) && pre[w] == usize::MAX {
                dfs(w, succ, inside, pre, fin, p, f);
            }
        }
        fin[v] = *f;
        *f += 1;
    }
    for &r in roots.iter().chain(within) {
        if inside(r) && pre[r] == usize::MAX {
            dfs(r, succ, &inside, &mut pre, &mut fin, &mut p, &mut f);
        }
    }
    // Reachability inside the subset, by closure.
    let mut reach = vec![vec![false; n]; n];
    for &v in within {
        for &w in &succ[v] {
            if inside(w) {
                reach[v][w] = true;
            }
        }
    }
    for &k in within {
        for &i in within {
            for &j in within {
                if reach[i][k] && reach[k][j] {
                    reach[i][j] = true;
                }
            }
        }
    }
    let mut heads: Vec<usize> = within
        .iter()
        .copied()
        .filter(|&v| {
            within
                .iter()
                .all(|&w| w == v || !(reach[v][w] && reach[w][v]) || pre[v] < pre[w])
        })
        .collect();
    heads.sort_by_key(|&h| std::cmp::Reverse(fin[h]));
    heads
        .into_iter()
        .map(|h| {
            let rest: Vec<usize> = within
                .iter()
                .copied()
                .filter(|&w| w != h && reach[h][w] && reach[w][h])
                .collect();
            if rest.is_empty() && !reach[h][h] {
                Element::Vertex(h)
            } else {
                let roots: Vec<usize> = succ[h]
                    .iter()
                    .copied()
                    .filter(|w| rest.contains(w))
                    .collect();
                Element::Component {
                    head: h,
                    body: declarative(succ, &rest, &roots),
                }
            }
        })
        .collect()
}

fn oracle(succ: &[Vec<usize>]) -> Vec<Element> {
    let all: Vec<usize> = (0..succ.len()).collect();
    declarative(succ, &all, &all)
}

fn random_graph(rng: &mut Rng) -> Vec<Vec<usize>> {
    let n = 1 + rng.below(10);
    (0..n)
        .map(|_| {
            let mut s: Vec<usize> = (0..rng.below(4)).map(|_| rng.below(n)).collect();
            zed_collections::sorted::sort_dedup(&mut s);
            s
        })
        .collect()
}

#[test]
fn bourdoncle_agrees_with_the_declarative_definition() {
    let mut rng = Rng::new(zed_tests::seed::seed(
        "bourdoncle_agrees_with_the_declarative_definition",
    ));
    for _ in 0..RANDOM_INSTANCES {
        agrees(&random_graph(&mut rng));
    }
    // A graph built to have a component: 0 -> 1 -> 2 -> 3 -> 0 is a cycle, so 0 to 3 are
    // mutually reachable and form one strongly connected component of four vertices, and a
    // component of more than one vertex is a `Component` element.
    assert!(
        agrees(&parser_loop())
            .iter()
            .any(|e| matches!(e, Element::Component { .. })),
        "the parser loop has a component"
    );
}

/// Asserts that the order of `g` is the declarative one, and returns it.
fn agrees(g: &[Vec<usize>]) -> Vec<Element> {
    let got = weak_topological_order(g);
    assert_eq!(show(&got), show(&oracle(g)), "graph {g:?}");
    got
}

/// A tokenizer's main loop: 0 reads a character, 1 classifies it, 2 accumulates a token and
/// loops on itself while the token continues, 3 emits it and returns to 0; 4 is the end of
/// input, reached from 1.
fn parser_loop() -> Vec<Vec<usize>> {
    vec![vec![1], vec![2, 4], vec![2, 3], vec![0], vec![]]
}

/// Whether `e` is a component with a component somewhere in its body.
fn nests(e: &Element) -> bool {
    matches!(e, Element::Component { body, .. }
        if body.iter().any(|b| matches!(b, Element::Component { .. }) || nests(b)))
}

/// The defining property of a weak topological order: every edge either goes forward in
/// the order, or goes to the head of a component that contains its source.
#[test]
fn every_backward_edge_goes_to_an_enclosing_head() {
    fn positions(e: &Element, heads: &mut Vec<usize>, out: &mut Vec<(usize, Vec<usize>)>) {
        match e {
            Element::Vertex(v) => out.push((*v, heads.clone())),
            Element::Component { head, body } => {
                heads.push(*head);
                out.push((*head, heads.clone()));
                for b in body {
                    positions(b, heads, out);
                }
                heads.pop();
            }
        }
    }
    let mut rng = Rng::new(zed_tests::seed::seed(
        "every_backward_edge_goes_to_an_enclosing_head",
    ));
    for _ in 0..RANDOM_INSTANCES / 4 {
        let g = random_graph(&mut rng);
        let mut order = Vec::new();
        for e in weak_topological_order(&g) {
            positions(&e, &mut Vec::new(), &mut order);
        }
        assert_eq!(order.len(), g.len(), "each vertex once: {g:?}");
        let at = |v: usize| order.iter().position(|(w, _)| *w == v).unwrap();
        for (u, ws) in g.iter().enumerate() {
            for &w in ws {
                if at(w) <= at(u) {
                    assert!(order[at(u)].1.contains(&w), "edge {u}->{w} in {g:?}");
                }
            }
        }
    }
}

#[test]
fn a_parser_loop_with_an_inner_retry_nests_its_components() {
    // A tokenizer's main loop: 0 reads a character, 1 classifies it, 2 accumulates a token
    // and loops on itself while the token continues, 3 emits it and returns to 0; 4 is the
    // end of input, reached from 1.
    let g = vec![vec![1], vec![2, 4], vec![2, 3], vec![0], vec![]];
    assert_eq!(show(&weak_topological_order(&g)), "(0 1 (2) 3) 4");
    assert_eq!(show(&oracle(&g)), "(0 1 (2) 3) 4");
}

#[test]
fn the_traversal_order_picks_the_head() {
    // The same three-cell loop with its cells numbered two ways: the head is whichever cell
    // the traversal reaches first, which is the first in number;
    // `ordered_by` numbers the vertices by their keys.
    assert_eq!(
        show(&weak_topological_order(&[vec![1], vec![2], vec![0]])),
        "(0 1 2)"
    );
    assert_eq!(
        show(&weak_topological_order(&[vec![2], vec![0], vec![1]])),
        "(0 2 1)"
    );
}

/// Larger graphs, with successor lists out of order and repeated, the traversal's order
/// following the lists as written.
#[test]
fn the_order_agrees_with_the_declarative_definition_on_larger_graphs() {
    let mut rng = Rng::new(zed_tests::seed::seed(
        "the_order_agrees_with_the_declarative_definition_on_larger_graphs",
    ));
    for _ in 0..RANDOM_INSTANCES / 2 {
        let n = 1 + rng.below(40);
        let g: Vec<Vec<usize>> = (0..n)
            .map(|v| {
                (0..rng.below(4))
                    .map(|_| {
                        // Mostly near, so that loops nest.
                        if rng.below(3) == 0 {
                            rng.below(n)
                        } else {
                            (v + 2 * n + rng.below(5) - 2) % n
                        }
                    })
                    .collect()
            })
            .collect();
        agrees(&g);
    }
    // A graph built to nest: the parser loop's component has head 0 (the root, first in
    // preorder). With the edges into 0 removed, 2 keeps its self-loop, so the order of the
    // rest of the component holds 2 as a component of its own: "(0 1 (2) 3) 4".
    assert!(
        agrees(&parser_loop()).iter().any(nests),
        "the parser loop nests a component"
    );
}

/// The keyed order: the declarative order with the roots taken in the order of the keys and
/// each successor list sorted by them.
#[test]
fn the_keyed_order_agrees_with_the_declarative_definition() {
    let mut rng = Rng::new(zed_tests::seed::seed(
        "the_keyed_order_agrees_with_the_declarative_definition",
    ));
    for _ in 0..RANDOM_INSTANCES {
        let g = random_graph(&mut rng);
        let n = g.len();
        // Distinct keys in a random order.
        let mut keys: Vec<u64> = (0..n as u64).map(|k| 7 * k + 3).collect();
        for i in (1..n).rev() {
            keys.swap(i, rng.below(i + 1));
        }
        let mut by: Vec<usize> = (0..n).collect();
        by.sort_by_key(|&v| keys[v]);
        let sorted: Vec<Vec<usize>> = g
            .iter()
            .map(|s| {
                let mut s = s.clone();
                s.sort_by_key(|&w| keys[w]);
                s
            })
            .collect();
        let all: Vec<usize> = (0..n).collect();
        assert_eq!(
            show(&ordered_by(&g, &keys).unwrap()),
            show(&declarative(&sorted, &all, &by)),
            "graph {g:?}, keys {keys:?}"
        );
    }
}
