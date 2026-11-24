//! The benchmarks of the structures and walks of TEST-dry-shared-units: each routine whose
//! cost this crate states, at `n` and `8n` (limit 10.5, goal 9).

use std::collections::BTreeMap;

use crate::scaling;
use crate::seed::Rng;
use crate::{
    BitSet, Compression, Diff, Dijkstra, IdSource, Keep, Lift, Linking, MinHeap, Order, UnionFind,
    Worklist, block_of_edges, dag_idom, kahn, make_after_needs, post_order, reach, sources,
};

/// A number spread over `0..m` by a multiplicative hash (Knuth's constant
/// `2^64 / golden ratio`, odd, so `i -> i * K` permutes the words): inputs with no order
/// a routine could exploit, the same at every run. Not random, though: taken mod `m`, its
/// value mod each power of two dividing `m` is a function of `i` alone, so its inputs at `n`
/// and `8n` differ in structure; a routine whose cost depends on that structure, as a search
/// does, takes [`random_weighted_graph`]'s draws instead (PERF-dijkstra-ratio-9).
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

/// A random graph of `m` nodes, each with 4 edges out to nodes drawn uniformly from `0..m`, of
/// weights drawn uniformly from `1..=10`: the same distribution at every size, drawn by
/// SplitMix64 ([`Rng`], whose comment cites Steele, Lea and Flood 2014) from the fixed seed 1.
///
/// Why not [`spread`] (PERF-dijkstra-ratio-9). Until 2026-11-20 this graph was built with
/// `spread(4v + k, m)` for the heads and `spread(v + k, 10) + 1` for the weights. `spread` is a
/// multiplicative hash taken mod `m`, so the residue of a head mod every power of two dividing
/// `m` is a function of `4v + k` alone (2^5 divides 100,000, 2^8 divides 800,000), and the weight
/// of edge `k` of `v` is the weight of edge `k - 1` of `v + 1`: the graphs at `n` and `8n` were
/// two differently structured graphs, not one family at two sizes. Their searches took 1.187
/// heap entries per node at 100,000 and 1.293 at 800,000 (the entries made stale by a later
/// lowering, below), and the bench measured T(8n)/T(n) = 9.672, above the 9.44 that
/// `8 ln(8n) / ln n` gives at n = 100,000. The same search at 12,500, 100,000, 800,000 and
/// 6,400,000 nodes took 1.297, 1.187, 1.293 and 1.349 entries per node, up and down, and the
/// ratios of its instructions were 8.42, 9.67 and 9.22: noise of the input, not a growth of the
/// search. On the graph drawn here the entries per node are 1.22 at every size from 12,500 to
/// 6,400,000 (the law of large numbers), and the ratio is what the search's cost predicts
/// (see the comment of [`Dijkstra`] in `heap.rs`, "Cost, measured").
fn random_weighted_graph(m: usize) -> Vec<Vec<(usize, u64)>> {
    let mut rng = Rng::new(1);
    (0..m)
        .map(|_| {
            (0..4)
                .map(|_| (rng.below(m), rng.below_u64(10) + 1))
                .collect::<Vec<_>>()
        })
        .collect()
}

/// Small instances: `dijkstra_agrees_with_bellman_ford_on_random_graphs`. O(e log e): see the
/// comment of [`Dijkstra`] in `heap.rs`, "Cost, measured", for the bound and for how the
/// measured instructions of this bench follow it.
#[test]
fn dijkstra_takes_n_log_n_time() {
    let n = 100_000;
    let graphs = scaling::inputs(n, random_weighted_graph);
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

/// Calls `draw` `m` times, split evenly over `threads` threads (`m` a multiple of `threads`).
///
/// The threads wait at a barrier until all have started, so they draw at once at every size.
/// Without it, at `n` = 2^20 (32,768 draws a thread) the first threads were done before the
/// last had started, and the draws met less contention than at `8n`: the compare-and-swap
/// draws measured 9.40, 9.99 and 10.27 times the instructions at `8n` in three runs (load 49 to
/// 51), where `fetch_add`, which never retries, measured 7.9.
fn draw_on_threads(m: usize, threads: usize, draw: &(dyn Fn() -> u64 + Sync)) {
    if threads == 1 {
        for _ in 0..m {
            std::hint::black_box(draw());
        }
        return;
    }
    let all_started = std::sync::Barrier::new(threads);
    // Each thread joined by its handle, which waits for it to end, so that its instructions are
    // counted: the end of the scope alone does not wait for that (`scaling`, the module comment;
    // FAIL-print-ring-bench-ratio).
    std::thread::scope(|s| {
        let hs: Vec<_> = (0..threads)
            .map(|_| {
                s.spawn(|| {
                    all_started.wait();
                    for _ in 0..m / threads {
                        std::hint::black_box(draw());
                    }
                })
            })
            .collect();
        for h in hs {
            h.join().unwrap_or_else(|p| std::panic::resume_unwind(p));
        }
    });
}

/// Small instances: `ids::tests`. O(1) a draw with no other thread drawing; see the comment
/// of [`IdSource::take`] for contention (FAIL-idsource-take-wrap-race). The draws on 1 and
/// on 32 threads are each checked at `n` and `8n`, and each is printed beside the same draws
/// by `AtomicU64::fetch_add`, which `take` used before it checked for the top by a compare
/// and swap: instructions (of the run's threads, by the meter) and elapsed nanoseconds.
#[test]
fn id_draws_take_linear_time_and_cost_near_fetch_add() {
    use std::sync::atomic::{AtomicU64, Ordering};
    for (threads, n) in [(1, 1 << 20), (32, 1 << 22)] {
        scaling::check_instructions_only(
            &format!("IdSource::next, n draws on {threads} threads"),
            n,
            1,
            |m| {
                let ids = IdSource::starting_at(1);
                draw_on_threads(m, threads, &|| ids.next());
            },
        );
        for m in [n, 8 * n] {
            let mut meter = scaling::Meter::new();
            let mut cost = |draw: &(dyn Fn() -> u64 + Sync)| {
                let start = std::time::Instant::now();
                let work = meter.work(|| draw_on_threads(m, threads, draw));
                (work.units, start.elapsed().as_nanos())
            };
            let ids = IdSource::starting_at(1);
            let (take_units, take_ns) = cost(&|| ids.next());
            let add = AtomicU64::new(1);
            let (add_units, add_ns) = cost(&|| add.fetch_add(1, Ordering::Relaxed));
            eprintln!(
                "ids: {m} draws on {threads} threads: take {take_units} instr {take_ns} ns, \
                 fetch_add {add_units} instr {add_ns} ns"
            );
        }
    }
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
            let mut uf = UnionFind::<(), Diff<i64>>::new(m, Compression::Halving, Linking::Rank);
            for i in 0..m {
                let (a, b) = (spread(2 * i, m), spread(2 * i + 1, m));
                let d = Diff(a as i64 - b as i64);
                let _ = uf.join(a, b, &d, Keep::Second, |_, _, _| {});
            }
            for v in 0..m {
                let (r, Diff(o)) = uf.find_offset(v);
                assert_eq!(o, v as i64 - r as i64);
            }
        },
    );
}
