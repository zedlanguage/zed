//! The weak topological order against its declarative definition.
//!
//! The definition, written here without Bourdoncle's stack: run a depth-first search from
//! the roots in order, visiting successors in source order, and number the vertices in
//! preorder and in finish order. Group the vertices into strongly connected components by
//! mutual reachability; a component's head is its member with the least preorder number,
//! and the components are listed by decreasing finish time of their heads. A component with
//! one vertex and no self-loop is that vertex; any other is the head followed by the order
//! of the rest of the component, computed the same way with the edges into the head removed
//! and the head's successors as roots.

use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zedc::store::wto::{Element, show, weak_topological_order};

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
            s.sort_unstable();
            s.dedup();
            s
        })
        .collect()
}

#[test]
fn bourdoncle_agrees_with_the_declarative_definition() {
    let mut rng = Rng::new(0x5f05);
    let mut components = 0;
    for _ in 0..4 * RANDOM_INSTANCES {
        let g = random_graph(&mut rng);
        let got = weak_topological_order(&g);
        assert_eq!(show(&got), show(&oracle(&g)), "graph {g:?}");
        components += got
            .iter()
            .filter(|e| matches!(e, Element::Component { .. }))
            .count();
    }
    // The sample exercises components, not only acyclic graphs.
    assert!(components > RANDOM_INSTANCES, "{components} components");
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
    let mut rng = Rng::new(0xb0d);
    for _ in 0..RANDOM_INSTANCES {
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
    // the traversal reaches first, which is the first in source order.
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
    let mut rng = Rng::new(0x5f06);
    let mut nested = 0;
    for _ in 0..2 * RANDOM_INSTANCES {
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
        let got = weak_topological_order(&g);
        assert_eq!(show(&got), show(&oracle(&g)), "graph {g:?}");
        fn nests(e: &Element) -> bool {
            matches!(e, Element::Component { body, .. }
                if body.iter().any(|b| matches!(b, Element::Component { .. }) || nests(b)))
        }
        if got.iter().any(nests) {
            nested += 1;
        }
    }
    // The sample exercises nested components.
    assert!(nested > RANDOM_INSTANCES / 4, "{nested} with nesting");
}
