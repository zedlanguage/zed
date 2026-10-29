//! The definedness-fix recursion checks (DESIGN.md sec:kernel, the dependency theorem): every
//! schedule of a definedness `fix` reaches the same family. Jacobi rounds (the wavefront),
//! chaotic iteration in seeded orders, and memoized pull all agree on the entries they
//! define, and on a cyclic dependency all stall on the same keys: the entries that depend,
//! directly or through others, on a cycle.

use std::collections::BTreeSet;

use zed_kernel::term::build::{if_, lit, prim, var};
use zed_kernel::{Evaluator, Family, KernelError, Pattern, Prim, Schedule, Term, Value, World};
use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zed_tests::kernel::*;

/// Every schedule the harness runs: the wavefront, memoized pull, and chaotic iteration in
/// eight seeded orders.
fn schedules() -> Vec<Schedule> {
    let mut out = vec![Schedule::Rounds, Schedule::Pull];
    out.extend((0..8).map(Schedule::Chaotic));
    out
}

fn run(t: &Term, schedule: Schedule) -> Result<Value, KernelError> {
    Evaluator::new(World::new()).with_schedule(schedule).run(t)
}

/// A directed graph on the nodes `0..n`, as its successor lists.
type Graph = Vec<Vec<i64>>;

/// The successor table `node -> successor -> true`. A node with no successors has no entry,
/// since an empty inner level drops its key.
fn successors(g: &Graph) -> Term {
    let leaves: Vec<_> = g
        .iter()
        .enumerate()
        .flat_map(|(u, vs)| vs.iter().map(move |&v| (u as i64, v)))
        .map(|(u, v)| (vec![Value::Int(u), Value::Int(v)], Value::Bool(true)))
        .collect();
    lit(Value::Family(Family::from_leaves(leaves).unwrap()))
}

/// The number of paths from each node to a sink, counting the empty path: a build system's
/// count of the ways each target's inputs reach the sources. `paths(u) = 1 + Σ paths(v)` over
/// the successors `v` of `u`.
fn path_counts(g: &Graph) -> Term {
    let nodes = lit(Value::Family(Family::set(0..g.len() as i64)));
    let succ = successors(g);
    fix_defined(nodes, |this, u| {
        let next = fresh("next");
        let through = fold(
            fam_with(var(&next), |v| get(this, v)),
            Term::PrimFn(Prim::Add),
            Some(lit(0)),
        );
        Term::Match(
            rc(get(succ, u)),
            vec![
                (Pattern::Atom("notFound".into(), vec![]), lit(1)),
                (Pattern::Bind(next.as_str().into()), add(lit(1), through)),
            ],
        )
    })
}

/// What `path_counts` must compute on `g`: the counts, or, when some node reaches a cycle,
/// the stall naming every such node.
fn expected(g: &Graph) -> Result<Value, KernelError> {
    let n = g.len();
    // A node reaches a cycle when it cannot be removed by repeatedly removing sinks.
    let mut count: Vec<Option<i64>> = vec![None; n];
    loop {
        let mut changed = false;
        for u in 0..n {
            if count[u].is_none() && g[u].iter().all(|&v| count[v as usize].is_some()) {
                count[u] = Some(
                    1 + g[u]
                        .iter()
                        .map(|&v| count[v as usize].unwrap())
                        .sum::<i64>(),
                );
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let stalled: Vec<Value> = (0..n as i64)
        .filter(|&u| count[u as usize].is_none())
        .map(Value::Int)
        .collect();
    if stalled.is_empty() {
        Ok(Value::Family(Family::of(
            count
                .iter()
                .enumerate()
                .map(|(u, c)| (u as i64, c.unwrap())),
        )))
    } else {
        Err(KernelError::Stalled { keys: stalled })
    }
}

/// Every directed graph on three nodes, self-loops included: 2^9 = 512 graphs.
fn all_graphs_on_three_nodes() -> Vec<Graph> {
    (0..512u32)
        .map(|bits| {
            (0..3)
                .map(|u| (0..3).filter(|v| bits >> (u * 3 + v) & 1 == 1).collect())
                .collect()
        })
        .collect()
}

/// Random graphs on 4 to 8 nodes. Half are acyclic under a random topological order, so
/// that key order and dependency order differ; the rest have arbitrary edges.
fn random_graphs(seed: u64) -> Vec<Graph> {
    let mut rng = Rng::new(seed);
    (0..RANDOM_INSTANCES)
        .map(|i| {
            let n = 4 + rng.below(5);
            let mut rank: Vec<usize> = (0..n).collect();
            for j in (1..n).rev() {
                rank.swap(j, rng.below(j + 1));
            }
            (0..n)
                .map(|u| {
                    (0..n)
                        .filter(|&v| {
                            let allowed = i % 2 == 1 || rank[u] > rank[v];
                            allowed && rng.below(3) == 0
                        })
                        .map(|v| v as i64)
                        .collect()
                })
                .collect()
        })
        .collect()
}

#[test]
fn every_schedule_counts_paths_on_every_three_node_graph_or_stalls_on_the_same_keys() {
    let mut stalls = 0;
    for g in all_graphs_on_three_nodes() {
        let want = expected(&g);
        stalls += want.is_err() as usize;
        let t = path_counts(&g);
        for sch in schedules() {
            assert_eq!(run(&t, sch), want, "{sch:?} on {g:?}");
        }
    }
    // Both outcomes are exercised: 25 of the 512 graphs are acyclic.
    assert_eq!(stalls, 512 - 25);
}

#[test]
fn every_schedule_agrees_on_random_graphs_with_dependencies_out_of_key_order() {
    let (mut acyclic, mut partly_stalled) = (0, 0);
    for g in random_graphs(21) {
        let want = expected(&g);
        match &want {
            Ok(_) => acyclic += 1,
            Err(KernelError::Stalled { keys }) if keys.len() < g.len() => partly_stalled += 1,
            Err(_) => {}
        }
        let t = path_counts(&g);
        for sch in schedules() {
            assert_eq!(run(&t, sch), want, "{sch:?} on {g:?}");
        }
    }
    // Both the defined case and a stall that leaves some entries defined occur.
    assert!(acyclic >= RANDOM_INSTANCES / 2, "{acyclic} acyclic");
    assert!(partly_stalled > 0);
}

/// The edit distance between `a` and `b`, as a definedness `fix` over the cells `(i, j)` of
/// its table: the distance between the first `i` characters of `a` and the first `j` of `b`.
fn edit_distance(a: &str, b: &str) -> Term {
    let (n, m) = (a.len() as i64, b.len() as i64);
    let cells: Vec<Value> = (0..=n)
        .flat_map(|i| (0..=m).map(move |j| Value::Tuple(vec![Value::Int(i), Value::Int(j)])))
        .collect();
    let chars = |w: &str| {
        lit(Value::Family(Family::of(
            w.chars()
                .enumerate()
                .map(|(k, c)| (k as i64, Value::str(&c.to_string()))),
        )))
    };
    let (ca, cb) = (chars(a), chars(b));
    fix_defined(lit(Value::Family(Family::set(cells))), |this, c| {
        let (i, j) = (nth(c.clone(), 0), nth(c, 1));
        let at = |di: i64, dj: i64| {
            get(
                this.clone(),
                prim(
                    Prim::Tuple,
                    vec![sub(i.clone(), lit(di)), sub(j.clone(), lit(dj))],
                ),
            )
        };
        let min = |x: Term, y: Term| prim(Prim::Min, vec![x, y]);
        let differ = if_(
            eq(
                get(ca, sub(i.clone(), lit(1))),
                get(cb, sub(j.clone(), lit(1))),
            ),
            lit(0),
            lit(1),
        );
        if_(
            eq(i.clone(), lit(0)),
            j.clone(),
            if_(
                eq(j.clone(), lit(0)),
                i.clone(),
                min(
                    min(add(at(1, 0), lit(1)), add(at(0, 1), lit(1))),
                    add(at(1, 1), differ),
                ),
            ),
        )
    })
}

/// The edit distance by the textbook table, for comparison.
fn levenshtein(a: &str, b: &str) -> i64 {
    let (a, b): (Vec<char>, Vec<char>) = (a.chars().collect(), b.chars().collect());
    let mut row: Vec<i64> = (0..=b.len() as i64).collect();
    for i in 1..=a.len() {
        let mut prev = row[0];
        row[0] = i as i64;
        for j in 1..=b.len() {
            let here = row[j];
            row[j] = (row[j] + 1)
                .min(row[j - 1] + 1)
                .min(prev + (a[i - 1] != b[j - 1]) as i64);
            prev = here;
        }
    }
    row[b.len()]
}

#[test]
fn edit_distance_top_down_memoized_equals_the_bottom_up_wavefront() {
    // Memoized pull computes the table on demand from the first cell in key order; the
    // wavefront fills it by anti-diagonals. Both give every cell the same value.
    let pairs = [
        ("kitten", "sitting"),
        ("flaw", "lawn"),
        ("", "abc"),
        ("intention", "execution"),
        ("same", "same"),
    ];
    for (a, b) in pairs {
        let t = edit_distance(a, b);
        let wave = run(&t, Schedule::Rounds).unwrap();
        for sch in schedules() {
            assert_eq!(run(&t, sch).as_ref(), Ok(&wave), "{sch:?} on {a:?}, {b:?}");
        }
        let corner = Value::Tuple(vec![Value::Int(a.len() as i64), Value::Int(b.len() as i64)]);
        assert_eq!(
            wave.as_family().unwrap().get(&corner),
            Some(&Value::Int(levenshtein(a, b))),
            "{a:?}, {b:?}"
        );
    }
}

#[test]
fn a_fix_nested_in_another_postpones_the_outer_entry_on_an_outer_read() {
    // Each department's cost is a running total over its three budget lines, computed by an
    // inner fix; line 0 starts from the cost of the department it reports to. A read of an
    // undefined outer entry inside the inner fix must postpone the outer entry, not stall the
    // inner fix, under every schedule.
    let reports_to = lit(Value::Family(Family::of(
        [("ops", "hq"), ("eng", "ops"), ("web", "eng")].map(|(d, p)| (s(d), s(p))),
    )));
    let lines = lit(Value::Family(Family::set(0..3i64)));
    let depts = lit(Value::Family(Family::set(
        ["web", "eng", "ops", "hq"].map(s),
    )));
    let cost = fix_defined(depts, |outer, d| {
        let running = fix_defined(lines, |inner, l| {
            let parent = get(outer, get(reports_to, d));
            let start = Term::Match(
                rc(parent),
                vec![
                    (Pattern::Atom("notFound".into(), vec![]), lit(100)),
                    (Pattern::Bind("p".into()), var("p")),
                ],
            );
            if_(
                eq(l.clone(), lit(0)),
                start,
                add(get(inner, sub(l.clone(), lit(1))), mul(l, lit(10))),
            )
        });
        get(running, lit(2))
    });
    // hq: 100 + 10 + 20 = 130; ops: 130 + 30 = 160; eng: 190; web: 220.
    let want = Value::Family(Family::of(
        [("eng", 190), ("hq", 130), ("ops", 160), ("web", 220)].map(|(d, c)| (s(d), Value::Int(c))),
    ));
    for sch in schedules() {
        assert_eq!(run(&cost, sch), Ok(want.clone()), "{sch:?}");
    }
}

#[test]
fn a_cycle_through_a_nested_fix_stalls_the_outer_entries_only() {
    // Two departments that report to each other: the outer fix stalls on both, and the inner
    // fix, whose own reads are all defined, is never the one reported.
    let reports_to = lit(Value::Family(Family::of(
        [("a", "b"), ("b", "a")].map(|(d, p)| (s(d), s(p))),
    )));
    let depts = lit(Value::Family(Family::set(["a", "b", "c"].map(s))));
    let cost = fix_defined(depts, |outer, d| {
        let running = fix_defined(lit(Value::Family(Family::set(0..2i64))), |inner, l| {
            if_(
                eq(l.clone(), lit(0)),
                add(get(outer, get(reports_to, d)), lit(0)),
                add(get(inner, sub(l, lit(1))), lit(1)),
            )
        });
        get(running, lit(1))
    });
    let stalled: BTreeSet<_> = ["a", "b"].map(s).into_iter().collect();
    for sch in schedules() {
        match run(&cost, sch) {
            Err(KernelError::Stalled { keys }) => {
                assert_eq!(
                    keys.into_iter().collect::<BTreeSet<_>>(),
                    stalled,
                    "{sch:?}"
                )
            }
            other => panic!("{sch:?}: expected a stall, got {other:?}"),
        }
    }
}
