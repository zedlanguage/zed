//! Direct tests of the structures and walks DRY-graph-shared put in this crate
//! (TEST-dry-shared-units): the ends of each (empty, one element, the marker values), each
//! documented precondition broken, property tests against a plain reference on random inputs,
//! and for each property a negative control: a plausible wrong version, on the test's own
//! inputs, that the test's reference tells apart from the right one.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, VecDeque};

use crate::seed::Rng;
use crate::{
    BitSet, Compression, Diff, Dijkstra, IdSource, Keep, Lift, Linking, MinHeap, Order, UnionFind,
    Worklist, biconnected, block_of_edges, components, dag_idom, kahn, make_after_needs, on_cycle,
    post_order, reach, sources, tarjan,
};

/// A random acyclic graph over `0..n`: edges only from a lower number to a higher one under a
/// random relabeling, so no order of the numbers is already topological.
fn random_dag(rng: &mut Rng, n: usize) -> Vec<Vec<usize>> {
    let mut label: Vec<usize> = (0..n).collect();
    rng.shuffle(&mut label);
    let mut kids = vec![Vec::new(); n];
    for a in 0..n {
        for b in a + 1..n {
            if rng.below(3) == 0 {
                kids[label[a]].push(label[b]);
            }
        }
    }
    kids
}

/// Whether every edge of `kids` goes from a node placed earlier in `order` to one placed later.
fn topological(kids: &[Vec<usize>], order: &[usize]) -> bool {
    let mut at = vec![usize::MAX; kids.len()];
    for (i, &v) in order.iter().enumerate() {
        at[v] = i;
    }
    order.iter().all(|&v| {
        kids[v]
            .iter()
            .all(|&c| at[c] != usize::MAX && at[v] < at[c])
    })
}

/// The nodes `roots` reach in `kids`, roots included, by a search with a plain flag per node.
fn reached(kids: &[Vec<usize>], roots: &[usize]) -> Vec<bool> {
    let mut seen = vec![false; kids.len()];
    let mut todo = roots.to_vec();
    while let Some(v) = todo.pop() {
        if !std::mem::replace(&mut seen[v], true) {
            todo.extend(&kids[v]);
        }
    }
    seen
}

mod bitset {
    use super::*;

    /// Room 0, the default set, and the bits at both ends of a word.
    #[test]
    fn the_ends_of_a_bit_set() {
        let mut a = BitSet::new(0);
        assert_eq!(a.iter().count(), 0);
        assert!(!a.contains(0) && !a.contains(usize::MAX));
        assert_eq!(a, BitSet::default());
        assert!(!a.union(&BitSet::default()));
        for i in [63, 64, 0] {
            assert!(a.insert(i));
        }
        assert_eq!(a.iter().collect::<Vec<_>>(), [0, 63, 64]);
        assert!(!a.contains(65) && !a.contains(62));
    }

    /// Inserts and unions of random sets with random room, against `BTreeSet`: each insert's
    /// and union's answer, membership, the ascending numbers, and equality.
    #[test]
    fn bit_sets_agree_with_ordered_sets() {
        let (mut rng, seed) = Rng::fresh("bit_sets_agree_with_ordered_sets");
        let mut grew = [0usize; 2];
        for _ in 0..2000 {
            let top = 1 + rng.below(300);
            let mut sets: Vec<(BitSet, BTreeSet<usize>)> = Vec::new();
            for _ in 0..2 {
                let room = rng.below(top + 1);
                let mut b = BitSet::new(room);
                let mut s = BTreeSet::new();
                for _ in 0..rng.below(20) {
                    let i = rng.below(top);
                    assert_eq!(b.insert(i), s.insert(i), "seed {seed}: insert {i}");
                }
                sets.push((b, s));
            }
            let (b1, s1) = sets.pop().expect("two sets");
            let (mut b0, mut s0) = sets.pop().expect("two sets");
            assert_eq!(b0 == b1, s0 == s1, "seed {seed}: {s0:?} and {s1:?}");
            let before = s0.len();
            let new = b0.union(&b1);
            s0.extend(&s1);
            assert_eq!(new, s0.len() > before, "seed {seed}");
            grew[usize::from(new)] += 1;
            assert_eq!(
                b0.iter().collect::<Vec<_>>(),
                s0.iter().copied().collect::<Vec<_>>()
            );
            for i in 0..top + 70 {
                assert_eq!(b0.contains(i), s0.contains(&i), "seed {seed}: {i}");
            }
        }
        assert!(grew[0] > 0 && grew[1] > 0, "{grew:?}");
    }

    /// Negative control for `bit_sets_agree_with_ordered_sets` and
    /// `sets_with_the_same_numbers_are_equal_whatever_their_room`: equality of the words, room
    /// and all, calls {5} with room 1000 and {5} with room 64 apart.
    #[test]
    fn equality_by_the_words_is_caught() {
        let (mut a, mut b) = (BitSet::new(1000), BitSet::new(64));
        a.insert(5);
        b.insert(5);
        assert_eq!(a, b);
        assert_ne!(format!("{a:?}"), format!("{b:?}"), "the words differ");
    }
}

mod worklist {
    use super::*;

    /// No items, no item queued, and `first(n, 0)`.
    #[test]
    fn the_ends_of_a_worklist() {
        assert_eq!(Worklist::all(0, Order::Fifo).pop(), None);
        assert_eq!(Worklist::new(0, Order::Lifo).pop(), None);
        let mut w = Worklist::first(3, 0, Order::Fifo);
        assert!((0..3).all(|i| !w.is_queued(i)));
        assert_eq!(w.pop(), None);
        let mut w = Worklist::first(1, 1, Order::Lifo);
        assert_eq!((w.pop(), w.pop()), (Some(0), None));
    }

    /// An item past `n` is refused with the index's panic (the list has no room for it).
    #[test]
    #[should_panic(expected = "index out of bounds: the len is 3 but the index is 3")]
    fn an_item_past_the_end_is_refused() {
        Worklist::new(3, Order::Fifo).push(3);
    }

    /// More items queued at the start than there are.
    #[test]
    #[should_panic(expected = "range end index 4 out of range for slice of length 3")]
    fn more_first_items_than_items_are_refused() {
        Worklist::first(3, 4, Order::Fifo);
    }

    /// The list against a queue and a set: random pushes and pops in both orders.
    fn agree(rng: &mut Rng, order: Order, wrong: bool) -> bool {
        let n = 1 + rng.below(10);
        let k = rng.below(n + 1);
        let mut w = Worklist::first(n, k, order);
        let mut model: VecDeque<usize> = (0..k).collect();
        for _ in 0..40 {
            if rng.coin() {
                let i = rng.below(n);
                let new = !model.contains(&i);
                if w.push(i) != new {
                    return false;
                }
                if new {
                    model.push_back(i);
                }
            } else {
                // The wrong model takes from the other end.
                let fifo = (order == Order::Fifo) != wrong;
                let want = if fifo {
                    model.pop_front()
                } else {
                    model.pop_back()
                };
                if w.pop() != want {
                    return false;
                }
            }
            if (0..n).any(|i| w.is_queued(i) != model.contains(&i)) {
                return false;
            }
        }
        true
    }

    #[test]
    fn worklists_agree_with_a_queue_and_a_set() {
        let (mut rng, seed) = Rng::fresh("worklists_agree_with_a_queue_and_a_set");
        for order in [Order::Fifo, Order::Lifo] {
            for _ in 0..2000 {
                assert!(agree(&mut rng, order, false), "seed {seed}: {order:?}");
            }
        }
    }

    /// Negative control: the model taken from the other end disagrees on some run.
    #[test]
    fn a_list_taken_from_the_wrong_end_is_caught() {
        let (mut rng, seed) = Rng::fresh("a_list_taken_from_the_wrong_end_is_caught");
        for order in [Order::Fifo, Order::Lifo] {
            assert!(
                (0..2000).any(|_| !agree(&mut rng, order, true)),
                "seed {seed}: {order:?}"
            );
        }
    }
}

mod ids {
    use super::*;

    /// `take(0)` draws nothing: the next draw is the same number.
    #[test]
    fn taking_no_numbers_draws_none() {
        let ids = IdSource::starting_at(7);
        assert_eq!(ids.take(0), 7);
        assert_eq!(ids.next(), 7);
        assert_eq!(ids.next(), 8);
    }

    /// The numbers up to `u64::MAX - 1` are drawn, leaving the count at `u64::MAX`.
    #[test]
    fn the_last_numbers_are_drawn() {
        let ids = IdSource::starting_at(u64::MAX - 2);
        assert_eq!(ids.take(2), u64::MAX - 2);
    }

    /// A draw that carries the count past `u64::MAX` is refused: the count would wrap to the
    /// low numbers and draw them again (TEST-dry-shared-units: before, the `fetch_add` wrapped
    /// silently).
    #[test]
    #[should_panic(expected = "drawing 2 numbers from 18446744073709551614 passes u64::MAX")]
    fn a_draw_past_the_largest_number_is_refused() {
        IdSource::starting_at(u64::MAX - 1).take(2);
    }
}

mod heap {
    use super::*;

    /// Random pushes, pops, peeks and clears against a sorted vector; the heap built from a
    /// list against the same pushes.
    fn agree(rng: &mut Rng, max_first: bool) -> bool {
        let start: Vec<(u8, u8)> = (0..rng.below(8))
            .map(|_| (rng.below(5) as u8, rng.below(5) as u8))
            .collect();
        let mut h: MinHeap<(u8, u8)> = start.iter().copied().collect();
        let mut model = start;
        for _ in 0..40 {
            model.sort_unstable();
            if max_first {
                model.reverse();
            }
            if h.len() != model.len() || h.is_empty() != model.is_empty() {
                return false;
            }
            if h.peek() != model.first() {
                return false;
            }
            match rng.below(9) {
                0 => {
                    h.clear();
                    model.clear();
                }
                1..=4 => {
                    let x = (rng.below(5) as u8, rng.below(5) as u8);
                    h.push(x);
                    model.push(x);
                }
                _ => {
                    let want = (!model.is_empty()).then(|| model.remove(0));
                    if h.pop() != want {
                        return false;
                    }
                }
            }
        }
        true
    }

    #[test]
    fn the_heap_agrees_with_a_sorted_list() {
        let (mut rng, seed) = Rng::fresh("the_heap_agrees_with_a_sorted_list");
        assert_eq!(MinHeap::<u8>::default().pop(), None);
        assert_eq!(MinHeap::<u8>::new().peek(), None);
        for _ in 0..3000 {
            assert!(agree(&mut rng, false), "seed {seed}");
        }
    }

    /// Negative control: a list sorted greatest first disagrees on some run.
    #[test]
    fn a_greatest_first_order_is_caught() {
        let (mut rng, seed) = Rng::fresh("a_greatest_first_order_is_caught");
        assert!((0..3000).any(|_| !agree(&mut rng, true)), "seed {seed}");
    }

    /// The least distances of a random graph with weights 0 to 9 from node 0, by Bellman-Ford:
    /// `n - 1` passes over every edge.
    fn bellman_ford(n: usize, edges: &[(usize, usize, i64)]) -> Vec<Option<i64>> {
        let mut d = vec![None; n];
        d[0] = Some(0);
        for _ in 1..n {
            for &(a, b, w) in edges {
                if let Some(x) = d[a]
                    && d[b].is_none_or(|y| x + w < y)
                {
                    d[b] = Some(x + w);
                }
            }
        }
        d
    }

    fn random_weighted(rng: &mut Rng) -> (usize, Vec<(usize, usize, i64)>) {
        let n = 1 + rng.below(10);
        let edges = (0..rng.below(3 * n + 1))
            .map(|_| {
                let (a, b) = (rng.below(n), rng.below(n));
                (a, b, rng.int(0, 9))
            })
            .collect();
        (n, edges)
    }

    /// The order nodes came up in: each at most once and by distance, never falling.
    fn settles_once(order: &[(i64, usize)]) -> bool {
        let mut seen = BTreeSet::new();
        order.iter().all(|&(_, v)| seen.insert(v)) && order.is_sorted_by_key(|&(d, _)| d)
    }

    /// Dijkstra with both kinds of labels against Bellman-Ford: each node comes up once, in
    /// order of distance, at its least distance; a node never reached has no label.
    #[test]
    fn dijkstra_agrees_with_bellman_ford_on_random_graphs() {
        let (mut rng, seed) = Rng::fresh("dijkstra_agrees_with_bellman_ford_on_random_graphs");
        for _ in 0..3000 {
            let (n, edges) = random_weighted(&mut rng);
            let want = bellman_ford(n, &edges);
            let mut map: Dijkstra<usize, i64, BTreeMap<usize, i64>> =
                Dijkstra::starting(BTreeMap::from([(0, 0)]), [0, 1]);
            let mut vec: Dijkstra<usize, i64, Vec<i64>> = Dijkstra::new(vec![i64::MAX; n]);
            assert!(vec.lower(0, 0));
            for (got, labels) in [
                {
                    let mut order = Vec::new();
                    while let Some((x, v)) = map.pop() {
                        order.push((x, v));
                        for &(_, b, w) in edges.iter().filter(|e| e.0 == v) {
                            map.lower(b, x + w);
                        }
                    }
                    let l = map.labels();
                    (
                        order,
                        (0..n).map(|v| l.get(&v).copied()).collect::<Vec<_>>(),
                    )
                },
                {
                    let mut order = Vec::new();
                    while let Some((x, v)) = vec.pop() {
                        order.push((x, v));
                        for &(_, b, w) in edges.iter().filter(|e| e.0 == v) {
                            vec.lower(b, x + w);
                        }
                    }
                    let l = vec.labels();
                    (
                        order,
                        l.iter().map(|&x| (x != i64::MAX).then_some(x)).collect(),
                    )
                },
            ] {
                assert!(settles_once(&got), "seed {seed}: {edges:?}: {got:?}");
                assert_eq!(labels, want, "seed {seed}: {edges:?}");
                let came: BTreeSet<usize> = got.iter().map(|&(_, v)| v).collect();
                let reachable: BTreeSet<usize> = (0..n).filter(|&v| want[v].is_some()).collect();
                assert_eq!(came, reachable, "seed {seed}: {edges:?}");
            }
        }
    }

    /// Negative control for `dijkstra_agrees_with_bellman_ford_on_random_graphs`: the search
    /// on a bare heap that takes every entry, without skipping one whose label has fallen since
    /// it was queued, brings a node up twice, which `settles_once` rejects. On `0 -9-> 1`,
    /// `0 -1-> 2 -1-> 1`, node 1 is queued at 9 and again at 2.
    #[test]
    fn stale_entries_taken_as_live_are_caught() {
        let edges = [(0, 1, 9), (0, 2, 1), (2, 1, 1)];
        let mut label = [0, i64::MAX, i64::MAX];
        let mut heap = MinHeap::new();
        heap.push((0i64, 0usize));
        let mut raw = Vec::new();
        while let Some((x, v)) = heap.pop() {
            raw.push((x, v));
            for &(_, b, w) in edges.iter().filter(|e| e.0 == v) {
                if x + w < label[b] {
                    label[b] = x + w;
                    heap.push((x + w, b));
                }
            }
        }
        assert_eq!(raw, [(0, 0), (1, 2), (2, 1), (9, 1)]);
        assert!(!settles_once(&raw));
    }
}

mod order {
    use super::*;

    /// No node: nothing placed, reached or visited, and `kids` never called.
    #[test]
    fn the_walks_of_no_nodes() {
        assert_eq!(sources(&[]).count(), 0);
        let never = |_: usize| -> Vec<usize> { unreachable!("no node is placed") };
        assert_eq!(kahn(&mut [], &mut Vec::new(), never, |_| ()), 0);
        reach(
            std::iter::empty::<usize>(),
            |_| true,
            |_| -> Vec<usize> { unreachable!("no root") },
        );
        post_order(
            &mut (),
            std::iter::empty::<usize>(),
            |_, _, _| unreachable!("no root"),
            |_, _| unreachable!("no root"),
        );
        make_after_needs(std::iter::empty::<usize>(), |_, _| unreachable!("no root"));
    }

    /// A count of edges below the edges `kids` gives breaks the caller's contract; the count
    /// would fall below 0.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "attempt to subtract with overflow")]
    fn a_count_below_the_edges_into_a_node_is_refused() {
        let kids = [vec![1, 1], vec![]];
        let mut waits = vec![0, 1];
        kahn(&mut waits, &mut vec![0], |v| kids[v].clone(), |_| ());
    }

    /// Kahn's order on random graphs, acyclic or not, from each kind of `Ready`: topological
    /// over the nodes it places, every node placed exactly when no cycle reaches it, and those
    /// left with a count above 0.
    #[test]
    fn kahn_places_exactly_the_nodes_no_cycle_reaches_in_a_topological_order() {
        let (mut rng, seed) =
            Rng::fresh("kahn_places_exactly_the_nodes_no_cycle_reaches_in_a_topological_order");
        let mut outcomes = [0usize; 2];
        for _ in 0..3000 {
            let n = 1 + rng.below(10);
            let mut kids = random_dag(&mut rng, n);
            if rng.coin() {
                let (a, b) = (rng.below(n), rng.below(n));
                kids[a].push(b);
            }
            let cyclic = on_cycle(&kids);
            let cycle_reaches: Vec<bool> = {
                let starts: Vec<usize> = (0..n).filter(|&v| cyclic[v]).collect();
                reached(&kids, &starts)
            };
            for kind in 0..3 {
                let mut waits = vec![0; n];
                for c in kids.iter().flatten() {
                    waits[*c] += 1;
                }
                let starts: Vec<usize> = sources(&waits).collect();
                let mut out = Vec::new();
                let placed = match kind {
                    0 => kahn(
                        &mut waits,
                        &mut starts.clone(),
                        |v| kids[v].clone(),
                        |v| out.push(v),
                    ),
                    1 => kahn(
                        &mut waits,
                        &mut VecDeque::from(starts.clone()),
                        |v| kids[v].clone(),
                        |v| out.push(v),
                    ),
                    _ => kahn(
                        &mut waits,
                        &mut starts
                            .iter()
                            .map(|&v| Reverse(v))
                            .collect::<BinaryHeap<_>>(),
                        |v| kids[v].clone(),
                        |v| out.push(v),
                    ),
                };
                assert_eq!(placed, out.len());
                let mut placed_set = vec![false; n];
                for &v in &out {
                    assert!(!placed_set[v], "seed {seed}: {v} placed twice");
                    placed_set[v] = true;
                }
                for v in 0..n {
                    assert_eq!(
                        placed_set[v], !cycle_reaches[v],
                        "seed {seed}: {kids:?}: {v}"
                    );
                    assert_eq!(waits[v] > 0, cycle_reaches[v], "seed {seed}: {kids:?}: {v}");
                }
                // The edges between placed nodes; a placed node may have an edge to one a cycle
                // reaches by another path.
                let sub: Vec<Vec<usize>> = (0..n)
                    .map(|v| kids[v].iter().copied().filter(|&c| placed_set[c]).collect())
                    .collect();
                assert!(topological(&sub, &out), "seed {seed}: {kids:?}: {out:?}");
                outcomes[usize::from(placed == n)] += 1;
            }
        }
        assert!(outcomes[0] > 0 && outcomes[1] > 0, "{outcomes:?}");
    }

    /// Negative control for the topological check: the reverse of Kahn's order of a graph with
    /// an edge is not topological.
    #[test]
    fn a_reversed_order_is_caught() {
        let kids = vec![vec![1], vec![]];
        assert!(topological(&kids, &[0, 1]));
        assert!(!topological(&kids, &[1, 0]));
    }

    /// `reach` on random graphs: the visited set is what the roots reach, each node's edges
    /// read once.
    #[test]
    fn reach_finds_what_the_roots_reach_reading_each_node_once() {
        let (mut rng, seed) = Rng::fresh("reach_finds_what_the_roots_reach_reading_each_node_once");
        for _ in 0..3000 {
            let n = 1 + rng.below(12);
            let mut kids = vec![Vec::new(); n];
            for _ in 0..rng.below(3 * n + 1) {
                let a = rng.below(n);
                kids[a].push(rng.below(n));
            }
            let roots: Vec<usize> = (0..rng.below(4)).map(|_| rng.below(n)).collect();
            let mut seen = vec![false; n];
            let mut read = vec![0; n];
            reach(
                roots.iter().copied(),
                |&v| !std::mem::replace(&mut seen[v], true),
                |&v| {
                    read[v] += 1;
                    kids[v].clone()
                },
            );
            let want = reached(&kids, &roots);
            assert_eq!(seen, want, "seed {seed}: {kids:?} from {roots:?}");
            for v in 0..n {
                assert_eq!(read[v], usize::from(want[v]), "seed {seed}: {kids:?}: {v}");
            }
        }
    }

    /// Negative control for `reach_finds_what_the_roots_reach_reading_each_node_once`: a
    /// search that keeps no visited set reads the foot of a diamond twice.
    #[test]
    fn a_search_without_a_visited_set_is_caught() {
        let kids = [vec![1, 2], vec![3], vec![3], vec![]];
        let mut read = [0; 4];
        let mut todo = vec![0];
        while let Some(v) = todo.pop() {
            read[v] += 1;
            todo.extend(&kids[v]);
        }
        assert_eq!(read[3], 2);
    }

    /// `post_order` and `make_after_needs` on random acyclic graphs with a memo: each node
    /// reached is left or made once, after every node below it.
    #[test]
    fn both_walks_finish_each_node_once_after_those_below_it() {
        let (mut rng, seed) = Rng::fresh("both_walks_finish_each_node_once_after_those_below_it");
        for _ in 0..3000 {
            let n = 1 + rng.below(10);
            let kids = random_dag(&mut rng, n);
            let roots: Vec<usize> = (0..1 + rng.below(3)).map(|_| rng.below(n)).collect();
            let want = reached(&kids, &roots);
            let mut left: Vec<usize> = Vec::new();
            post_order(
                &mut left,
                roots.iter().copied(),
                |left, &v, out| {
                    let new = !left.contains(&v);
                    if new {
                        out.extend(&kids[v]);
                    }
                    new
                },
                |left, v| left.push(v),
            );
            let mut made: Vec<usize> = Vec::new();
            let mut calls = 0;
            make_after_needs(roots.iter().copied(), |&v, needs| {
                calls += 1;
                if made.contains(&v) {
                    return true;
                }
                needs.extend(kids[v].iter().filter(|c| !made.contains(c)));
                if needs.is_empty() {
                    made.push(v);
                }
                needs.is_empty()
            });
            for order in [&left, &made] {
                let mut sorted = order.clone();
                sorted.sort_unstable();
                sorted.dedup();
                assert_eq!(sorted.len(), order.len(), "seed {seed}: {order:?} repeats");
                let set: Vec<bool> = (0..n).map(|v| order.contains(&v)).collect();
                assert_eq!(set, want, "seed {seed}: {kids:?} from {roots:?}");
                // Below before above: the reverse is topological.
                let rev: Vec<usize> = order.iter().rev().copied().collect();
                let sub: Vec<Vec<usize>> = (0..n)
                    .map(|v| if want[v] { kids[v].clone() } else { Vec::new() })
                    .collect();
                assert!(topological(&sub, &rev), "seed {seed}: {kids:?}: {order:?}");
            }
            // Each node is tried at most once to find what it lacks and once per push after.
            let pushes: usize = (0..n).filter(|&v| want[v]).map(|v| kids[v].len()).sum();
            assert!(
                calls <= 2 * n + pushes + roots.len(),
                "seed {seed}: {calls}"
            );
        }
    }
}

mod lift {
    use super::*;

    /// A tree of the root alone: `Lift::new(0)` and a shallow tree with no levels to spare
    /// (DRY-empty-lift-levels sized levels from the deepest jump; `deepest` 0 still keeps one
    /// level, the parent, so a node hung from the root has one).
    #[test]
    fn the_ends_of_a_lifted_tree() {
        let t = Lift::new(0);
        assert_eq!(
            (t.root(), t.depth(0), t.parent(0), t.lca(0, 0)),
            (0, 0, 0, 0)
        );
        assert_eq!(t.up_to(0, 5), 0);
        let iv = t.intervals();
        assert_eq!((iv.pre, iv.last), (vec![0], vec![0]));
        let mut t = Lift::with_depth(3, 0);
        // The root's depth is 0, so a node hung from it is at depth 1, one past `deepest` 0;
        // one level still holds it, since `2^1 > 1`.
        t.attach(0, 3);
        assert_eq!(
            (t.parent(0), t.depth(0), t.lca(0, 3), t.up_to(0, 0)),
            (3, 1, 3, 3)
        );
    }

    /// `with_depth` keeps enough levels for every depth up to `deepest`: on random trees no
    /// deeper than it, the shallow tree agrees with the full one on every query.
    #[test]
    fn a_tree_made_for_its_depth_agrees_with_one_made_for_every_depth() {
        let (mut rng, seed) =
            Rng::fresh("a_tree_made_for_its_depth_agrees_with_one_made_for_every_depth");
        for _ in 0..500 {
            let n = 1 + rng.below(40);
            let mut parent = vec![n; n];
            let mut depth = vec![0; n + 1];
            for v in 0..n {
                let p = rng.below(v + 1);
                let p = if p == v { n } else { p };
                parent[v] = p;
                depth[v] = depth[p] + 1;
            }
            let deepest = *depth.iter().max().expect("the root");
            let (mut full, mut shallow) = (Lift::new(n), Lift::with_depth(n, deepest));
            for (v, &p) in parent[..n].iter().enumerate() {
                full.attach(v, p);
                shallow.attach(v, p);
            }
            for a in 0..=n {
                for b in 0..=n {
                    assert_eq!(shallow.lca(a, b), full.lca(a, b), "seed {seed}: {a} {b}");
                }
                for d in 0..=deepest {
                    assert_eq!(shallow.up_to(a, d), full.up_to(a, d), "seed {seed}");
                }
            }
        }
    }

    /// Negative control for `the_lowest_common_ancestor_agrees_with_the_walk_up_the_parents`:
    /// the common ancestor found by climbing both nodes a step at a time, without first lifting
    /// the deeper one to the other's depth, is wrong on a node and its own parent: they meet
    /// only at the root.
    #[test]
    fn a_common_ancestor_without_the_lift_to_one_depth_is_caught() {
        let mut t = Lift::new(2);
        t.attach(0, 2);
        t.attach(1, 0);
        let wrong = |mut a: usize, mut b: usize| {
            while a != b {
                (a, b) = (t.parent(a), t.parent(b));
            }
            a
        };
        assert_eq!(t.lca(1, 0), 0);
        assert_eq!(wrong(1, 0), 2);
    }

    #[test]
    #[should_panic(expected = "a tree of 4294967295 nodes does not fit in memory")]
    fn a_tree_of_u32_max_nodes_is_refused() {
        Lift::with_depth(u32::MAX as usize, 1);
    }

    /// A node deeper than the tree was made for: levels for depths up to 1 (one level, since
    /// `2^1 > 1`) hold a node at depth 1, and a node at depth 2 is refused.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "node 1 is deeper than the depth the tree was made for")]
    fn a_node_deeper_than_the_levels_is_refused() {
        let mut t = Lift::with_depth(2, 1);
        t.attach(0, 2);
        t.attach(1, 0);
    }

    /// The dominator tree of no node, and of nodes left out of the order.
    #[test]
    fn the_dominators_of_no_node_and_of_nodes_left_out() {
        let t = dag_idom(0, &[], |_| Vec::<usize>::new());
        assert_eq!(t.root(), 0);
        // 0 -> 1, with 1 left out: 0 hangs from the root and 1 is not in the tree.
        let kids = [vec![1], vec![]];
        let t = dag_idom(2, &[0], |v| kids[v].clone());
        assert_eq!((t.parent(0), t.depth(0), t.depth(1)), (2, 1, 0));
    }
}

mod union_find {
    use super::*;

    /// No element, then one pushed.
    #[test]
    fn the_ends_of_the_disjoint_sets() {
        let mut uf = UnionFind::<(), ()>::new(0, Compression::Halving, Linking::Rank);
        assert!(uf.is_empty());
        assert_eq!(uf.push(), 0);
        assert_eq!((uf.len(), uf.find(0), uf.find_shared(0)), (1, 0, 0));
        assert!(!uf.union(0, 0) && !uf.union_into(0, 0) && !uf.union_least(0, 0));
        assert!(uf.same(0, 0));
        let mut off = UnionFind::<(), Diff<i64>>::new(1, Compression::Halving, Linking::Rank);
        assert_eq!(off.find_offset(0), (0, Diff(0)));
        let none = |_: &mut (), _: (), _: &Diff<i64>| {};
        assert_eq!(off.join(0, 0, &Diff(0), Keep::Second, none), Err(Diff(0)));
        assert_eq!(off.join(0, 0, &Diff(1), Keep::Second, none), Err(Diff(0)));
    }

    #[test]
    #[should_panic(expected = "index out of bounds: the len is 2 but the index is 2")]
    fn an_element_past_the_end_is_refused() {
        UnionFind::<(), ()>::new(2, Compression::Halving, Linking::Rank).find(2);
    }

    /// Negative control for `union_find_classes_match_a_plain_labeling`: a union that points
    /// `b` itself, not `b`'s root, at `a`'s root cuts `b` from the rest of its class, which
    /// the labeling sees: after joining {0, 1}, joining 1 to 2 moves 1 alone and leaves 0
    /// apart from 2.
    #[test]
    fn a_union_that_moves_the_element_not_its_root_is_caught() {
        let mut parent: Vec<usize> = (0..3).collect();
        let root = |p: &[usize], mut x: usize| {
            while p[x] != x {
                x = p[x];
            }
            x
        };
        for (a, b) in [(0, 1), (2, 1)] {
            let ra = root(&parent, a);
            parent[b] = ra;
        }
        let mut uf = UnionFind::<(), ()>::new(3, Compression::Halving, Linking::Rank);
        uf.union(0, 1);
        uf.union(2, 1);
        assert!(uf.same(0, 2));
        assert_ne!(root(&parent, 0), root(&parent, 2));
    }

    /// The rank saturates, not overflows, when a caller's chosen roots build a chain taller
    /// than 255: each `union_into(v + 1, v)` puts the old root under a new one, raising the
    /// rank by one each time. With a plain `+ 1` in `link` the 256th union overflows the byte
    /// (a panic in a debug build). The classes stay right.
    #[test]
    fn a_chain_of_chosen_roots_saturates_the_rank() {
        let mut uf = UnionFind::<(), ()>::new(300, Compression::Halving, Linking::Rank);
        for v in 0..299 {
            assert!(uf.union_into(v + 1, v));
        }
        assert_eq!(uf.find_shared(0), 299);
        assert!(uf.same(0, 299));
        assert!(!uf.union(0, 150));
    }
}

mod scc {
    use super::*;

    /// No node: no component, no cycle, nothing found.
    #[test]
    fn the_components_of_no_node() {
        let none: Vec<Vec<usize>> = Vec::new();
        assert!(components(&none, |&w| w).is_empty());
        assert!(on_cycle(&none).is_empty());
        let mut found = 0;
        tarjan(0, 0..0, |v| &none[v], |&w| Some(w), |_| found += 1);
        assert_eq!(found, 0);
    }

    /// Negative control for
    /// `components_are_the_classes_of_mutual_reach_numbered_in_reverse_topological_order`:
    /// the components of the graph with its edges reversed are the same classes but in a
    /// topological order, not a reverse one, which the test's check of each edge sees.
    #[test]
    fn components_in_topological_order_are_caught() {
        let edges = vec![vec![1], vec![]];
        let back = vec![vec![], vec![0]];
        let (right, wrong) = (components(&edges, |&w| w), components(&back, |&w| w));
        assert!(right[1] <= right[0]);
        assert!(wrong[1] > wrong[0]);
    }

    /// A walk over edge lists that records each component found, sorted, with the node it was
    /// reached from.
    struct Recorded<'g> {
        edges: &'g [Vec<usize>],
        found: Vec<(Vec<usize>, Option<usize>)>,
    }

    impl crate::Walk for Recorded<'_> {
        type At = usize;
        fn next(&mut self, v: usize, at: &mut usize) -> Option<usize> {
            let w = self.edges[v].get(*at).copied();
            *at += 1;
            w
        }
        fn found(&mut self, members: &mut [usize], from: Option<usize>) {
            let mut m = members.to_vec();
            m.sort_unstable();
            self.found.push((m, from));
        }
    }

    /// `Search::default()` is a search that has reached no node, as `Search::new()` is: both
    /// find the same components in the same order, and a second run over roots already reached
    /// finds nothing.
    #[test]
    fn a_default_search_is_a_new_one() {
        let edges = vec![vec![1], vec![0, 2], vec![], vec![3]];
        let run = |mut s: crate::Search<usize>| {
            let mut w = Recorded {
                edges: &edges,
                found: Vec::new(),
            };
            s.run(&mut w, 0..4);
            s.run(&mut w, 0..4);
            w.found
        };
        let got = run(crate::Search::default());
        assert_eq!(got, run(crate::Search::new()));
        assert_eq!(
            got,
            [(vec![2], Some(1)), (vec![0, 1], None), (vec![3], None)]
        );
    }

    /// Negative control for `a_node_is_on_a_cycle_exactly_when_it_reaches_itself`: membership
    /// in a component of two or more nodes alone misses a self-loop.
    #[test]
    fn a_cycle_test_that_misses_self_loops_is_caught() {
        let edges = vec![vec![0]];
        let comp = components(&edges, |&w| w);
        let wrong = comp.iter().filter(|&&c| c == comp[0]).count() > 1;
        assert!(on_cycle(&edges)[0] && !wrong);
    }
}

mod blocks {
    use super::*;

    /// No node, a node with no edge, and every node excluded but one.
    #[test]
    fn the_blocks_of_no_edge() {
        assert_eq!(block_of_edges(&[], 0, None), (0, vec![]));
        assert_eq!(block_of_edges(&[vec![]], 0, None), (0, vec![]));
        assert_eq!(block_of_edges(&[vec![]], 0, Some(0)), (0, vec![]));
        // A self-loop at the excluded node is in no block.
        let adj = vec![vec![(0, 0), (0, 0)]];
        assert_eq!(block_of_edges(&adj, 1, Some(0)), (0, vec![usize::MAX]));
        let mut found = Vec::new();
        biconnected(&adj, 1, None, |es| found.push(es.to_vec()));
        assert_eq!(found, [vec![0]]);
    }
}
