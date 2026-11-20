//! The benchmarks of the structures and walks of TEST-dry-shared-units: each routine whose
//! cost this crate states, at `n` and `8n` (limit 10.5, goal 9).

use std::collections::BTreeMap;

use crate::scaling;
use crate::{
    BitSet, Dijkstra, Lift, MinHeap, OffsetUnionFind, Order, Worklist, block_of_edges, dag_idom,
    kahn, make_after_needs, post_order, reach, sources,
};

/// A number spread over `0..m` by a multiplicative hash (Knuth's constant
/// `2^64 / golden ratio`, odd, so `i -> i * K` permutes the words): inputs with no order
/// a routine could exploit, the same at every run.
fn spread(i: usize, m: usize) -> usize {
    (i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) as usize % m
}

/// An acyclic graph of `m` nodes and up to `3m` edges, from `v` to `2v + 1`, `2v + 2` and
/// `v + 1` when below `m`: shared parts reached by many paths.
fn dag(m: usize) -> Vec<Vec<usize>> {
    (0..m)
        .map(|v| {
            [2 * v + 1, 2 * v + 2, v + 1]
                .into_iter()
                .filter(|&w| w < m)
                .collect()
        })
        .collect()
}

/// Small instances: `bit_sets_agree_with_ordered_sets`. O(words) for the union, O(words +
/// numbers) for the walk.
#[test]
fn the_union_and_walk_of_bit_sets_take_linear_time() {
    let n = 1 << 20;
    let sets = scaling::inputs(n, |m| {
        let (mut a, mut b) = (BitSet::new(m), BitSet::new(m));
        for i in 0..m / 4 {
            a.insert(spread(i, m));
            b.insert(spread(i + m, m));
        }
        (a, b)
    });
    scaling::check(
        "the union of two bit sets of n bits and the walk of it",
        n,
        |m| {
            let (a, b) = &sets[&m];
            let mut u = a.clone();
            u.union(b);
            assert!(u.iter().count() >= m / 4);
        },
    );
}

/// Small instances: `the_heap_agrees_with_a_sorted_list`. n pushes and pops of O(log n).
#[test]
fn n_pushes_and_pops_of_the_heap_take_n_log_n_time() {
    let n = 100_000;
    scaling::check("n pushes then n pops of a heap", n, |m| {
        let mut h = MinHeap::new();
        for i in 0..m {
            h.push(spread(i, m));
        }
        let mut last = 0;
        while let Some(x) = h.pop() {
            assert!(x >= last);
            last = x;
        }
    });
}

/// Small instances: `the_heap_agrees_with_a_sorted_list`. Building from a list is O(n),
/// not n pushes.
#[test]
fn a_heap_built_from_a_list_takes_linear_time() {
    let n = 1 << 20;
    let lists = scaling::inputs(n, |m| (0..m).map(|i| spread(i, m)).collect::<Vec<_>>());
    scaling::check("a heap of n elements built from a list", n, |m| {
        let h: MinHeap<usize> = lists[&m].iter().copied().collect();
        assert_eq!(h.len(), m);
    });
}

/// Small instances: `dijkstra_agrees_with_bellman_ford_on_random_graphs`. O(e log e).
#[test]
fn dijkstra_takes_n_log_n_time() {
    let n = 100_000;
    let graphs = scaling::inputs(n, |m| {
        (0..m)
            .map(|v| {
                (0..4)
                    .map(|k| (spread(4 * v + k, m), (spread(v + k, 10) + 1) as u64))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    });
    scaling::check("Dijkstra on n nodes and 4n edges", n, |m| {
        let g = &graphs[&m];
        let mut d: Dijkstra<usize, u64, Vec<u64>> = Dijkstra::new(vec![u64::MAX; m]);
        d.lower(0, 0);
        let mut settled = 0;
        while let Some((x, v)) = d.pop() {
            settled += 1;
            for &(w, c) in &g[v] {
                d.lower(w, x + c);
            }
        }
        assert!(settled > 0);
    });
}

/// Small instances: `kahn_places_exactly_the_nodes_no_cycle_reaches_in_a_topological_order`.
/// O(n + e).
#[test]
fn kahn_takes_linear_time() {
    let n = 200_000;
    let graphs = scaling::inputs(n, dag);
    scaling::check("Kahn's order of n nodes and 3n edges", n, |m| {
        let g = &graphs[&m];
        let mut waits = vec![0; m];
        for &c in g.iter().flatten() {
            waits[c] += 1;
        }
        let mut ready: Vec<usize> = sources(&waits).collect();
        let placed = kahn(&mut waits, &mut ready, |v| g[v].iter().copied(), |_| ());
        assert_eq!(placed, m);
    });
}

/// Small instances: `reach_finds_what_the_roots_reach_reading_each_node_once`. O(n + e).
#[test]
fn reach_takes_linear_time() {
    let n = 200_000;
    let graphs = scaling::inputs(n, dag);
    scaling::check("the search of n nodes and 3n edges from one root", n, |m| {
        let g = &graphs[&m];
        let mut seen = vec![false; m];
        reach(
            [0],
            |&v| !std::mem::replace(&mut seen[v], true),
            |&v| g[v].iter().copied(),
        );
        assert!(seen.iter().all(|&s| s));
    });
}

/// Small instances: `both_walks_finish_each_node_once_after_those_below_it`. O(n + e)
/// each.
#[test]
fn post_order_and_make_after_needs_take_linear_time() {
    let n = 200_000;
    let graphs = scaling::inputs(n, dag);
    scaling::check("the post-order of n nodes and 3n edges", n, |m| {
        let g = &graphs[&m];
        let mut left = vec![false; m];
        let mut count = 0;
        post_order(
            &mut left,
            [0],
            |left, &v, kids| {
                if left[v] {
                    return false;
                }
                kids.extend(&g[v]);
                true
            },
            |left, v| {
                // A node pushed by two parents is entered twice before it is left once;
                // only the first leaving counts.
                if !std::mem::replace(&mut left[v], true) {
                    count += 1;
                }
            },
        );
        assert_eq!(count, m);
    });
    scaling::check(
        "the nodes made after their needs, n nodes and 3n edges",
        n,
        |m| {
            let g = &graphs[&m];
            let mut made = vec![false; m];
            make_after_needs([0], |&v, needs| {
                if made[v] {
                    return true;
                }
                needs.extend(g[v].iter().filter(|&&c| !made[c]));
                made[v] = needs.is_empty();
                made[v]
            });
            assert!(made.iter().all(|&x| x));
        },
    );
}

/// A random tree of `m` nodes: node `v` hangs from a node before it or the root `m`.
fn tree(m: usize) -> Vec<usize> {
    (0..m)
        .map(|v| match spread(v, v + 1) {
            p if p == v => m,
            p => p,
        })
        .collect()
}

/// Small instances: `a_tree_made_for_its_depth_agrees_with_one_made_for_every_depth` and
/// `the_lowest_common_ancestor_agrees_with_the_walk_up_the_parents`. O(n log n) to attach
/// and query, O(n) for the intervals.
#[test]
fn lifting_a_tree_takes_n_log_n_time() {
    let n = 100_000;
    let trees = scaling::inputs(n, tree);
    scaling::check("n nodes attached and n common ancestors", n, |m| {
        let parent = &trees[&m];
        let mut t = Lift::new(m);
        for (v, &p) in parent.iter().enumerate() {
            t.attach(v, p);
        }
        let mut sum = 0;
        for v in 0..m {
            sum += t.lca(v, spread(v + m, m));
        }
        assert!(sum > 0);
    });
    let lifted: BTreeMap<usize, Lift> = trees
        .iter()
        .map(|(&m, parent)| {
            let mut t = Lift::new(m);
            for (v, &p) in parent.iter().enumerate() {
                t.attach(v, p);
            }
            (m, t)
        })
        .collect();
    scaling::check("the preorder intervals of a tree of n nodes", n, |m| {
        let iv = lifted[&m].intervals();
        assert_eq!(iv.pre.len(), m + 1);
    });
}

/// Small instances: `immediate_dominators_do_not_depend_on_the_topological_order_on_random_dags`.
/// O((n + e) log n).
#[test]
fn the_dominators_of_a_dag_take_n_log_n_time() {
    let n = 100_000;
    let graphs = scaling::inputs(n, dag);
    // `dag` has edges only from a lower number to a higher one, so `0..m` is an order.
    let orders = scaling::inputs(n, |m| (0..m).collect::<Vec<_>>());
    scaling::check("the dominator tree of n nodes and 3n edges", n, |m| {
        let g = &graphs[&m];
        let t = dag_idom(m, &orders[&m], |v| g[v].iter().copied());
        assert_eq!(t.parent(0), m);
    });
}

/// Small instances: `blocks_are_the_classes_no_cut_node_separates_on_random_multigraphs`.
/// O(n + e).
#[test]
fn the_blocks_of_a_graph_take_linear_time() {
    let n = 200_000;
    // A path `v - v + 1` with a chord `v - v + 3` at every fourth node: blocks of a few
    // edges strung along the path.
    let graphs = scaling::inputs(n, |m| {
        let mut adj = vec![Vec::new(); m];
        let mut e = 0;
        for v in 0..m {
            for w in [v + 1, if v % 4 == 0 { v + 3 } else { m }] {
                if w < m {
                    adj[v].push((w, e));
                    adj[w].push((v, e));
                    e += 1;
                }
            }
        }
        (adj, e)
    });
    scaling::check("the blocks of n nodes and 1.25n edges", n, |m| {
        let (adj, e) = &graphs[&m];
        let (blocks, _) = block_of_edges(adj, *e, None);
        assert!(blocks > 0);
    });
}

/// Small instances: `worklists_agree_with_a_queue_and_a_set`. O(1) a push and a pop.
#[test]
fn a_worklist_takes_linear_time() {
    let n = 1 << 20;
    for order in [Order::Fifo, Order::Lifo] {
        scaling::check(
            &format!("a {order:?} worklist of n items, each queued twice"),
            n,
            |m| {
                let mut w = Worklist::all(m, order);
                let mut taken = 0;
                while let Some(i) = w.pop() {
                    taken += 1;
                    if i % 2 == 0 {
                        w.push(i + 1);
                    }
                }
                assert!(taken >= m);
            },
        );
    }
}

/// Small instances: `offset_union_find_matches_plain_values`. O(m log_{1 + m/n} n) for m
/// operations with the root chosen.
#[test]
fn the_offset_union_find_takes_n_log_n_time() {
    let n = 100_000;
    scaling::check(
        "n offset unions of random pairs and a find of each",
        n,
        |m| {
            let mut uf: OffsetUnionFind<i64> = OffsetUnionFind::new(m);
            for i in 0..m {
                let (a, b) = (spread(2 * i, m), spread(2 * i + 1, m));
                let _ = uf.union_into(b, a, &(a as i64 - b as i64));
            }
            for v in 0..m {
                let (r, o) = uf.find(v);
                assert_eq!(o, v as i64 - r as i64);
            }
        },
    );
}
