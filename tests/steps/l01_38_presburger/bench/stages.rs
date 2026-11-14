//! The benchmarks of `stages.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::scaling::decides;
use crate::stages::*;
use zed_tests::scaling;
use zedc::store::int::Int;
use zedc::store::presburger::{Formula, Refusal, decide, satisfiable};
use zedc::store::utvpi::{Search, integer_empty, integer_empty_by};

#[test]
fn the_acyclic_hub_scales() {
    // Through the parity test itself: through `decide` the work around it hides the search's.
    let (small, large) = (hub(512, false), hub(scaling::FACTOR * 512, false));
    assert!(!raced(512, &small) && !raced(scaling::FACTOR * 512, &large));
    scaling::check("the acyclic hub", 512, |n| {
        let rows = if n == 512 { &small } else { &large };
        std::hint::black_box(raced(n, rows));
    });
}

#[test]
fn a_cycle_of_negative_edges_scales() {
    for n in [4, 5, 64] {
        let f = negchain(n);
        let m = satisfiable(&f).expect("decided").expect("a point");
        assert!(f.holds(&m), "{m:?}");
        // With `x0 >= x[n-1] + n + 3` as well, the rows of `d = 1` give
        // `x[n-1] >= x0 + n - 1`, so `x0 >= x0 + 2n + 2`: no point.
        let c = n as i64 + 3;
        let tight = Formula::and(vec![f, ge(&[(0, 1), (n - 1, -1)], -c)]);
        answers(&tight, Ok(false));
    }
    // From 2048 variables (6144 rows), so that a quadratic step is caught however cheap the
    // work per pair of rows: a scan of all rows per row comparing only their lengths gave
    // 18.8 times from 512 and passed, and gives 43.5 times from 2048 (2026-11-05, load 78).
    decides("a cycle of negative edges", 2048, Ok(true), negchain);
}

#[test]
fn the_cyclic_hub_scales() {
    // Goldberg and Radzik's search takes three passes at both sizes; Bellman–Ford–Moore took
    // 41.9 times the work (measured on this branch; XT3 measured 42.5).
    let (small, large) = (hub(512, true), hub(scaling::FACTOR * 512, true));
    assert!(!raced(512, &small) && !raced(scaling::FACTOR * 512, &large));
    scaling::check("the cyclic hub", 512, |n| {
        let rows = if n == 512 { &small } else { &large };
        std::hint::black_box(raced(n, rows));
    });
}

#[test]
fn bad_gor_scales() {
    // Goldberg and Radzik's search alone takes 129 passes at k = 256 and 1,026 at k = 2,048:
    // 59.8 times the work (78.2M to 4.68G instructions, measured on this branch as the negative
    // control and not kept; XT3 measured 62). The race with BF-Dijkstra and Duong's search
    // takes 26.8M to 209M instructions, 7.8 times (COMPLEXITY.md C24).
    let (small, large) = (bad_gor(256, 1), bad_gor(scaling::FACTOR * 256, 1));
    assert!(!raced(small.0, &small.1) && !raced(large.0, &large.1));
    scaling::check("BAD-GOR augmented, by k", 256, |k| {
        let (n, rows) = if k == 256 { &small } else { &large };
        std::hint::black_box(raced(*n, rows));
    });
}

#[test]
fn the_race_costs_little_more_than_duong_where_duong_wins() {
    // At k = 1,024 Duong's search finishes first. With the quick pairs stopped once their
    // units exceed those it expects still to need, the race took 2.9 times its instructions
    // (6.6G against 2.3G, load 7); with a step of each pair after every unit of Duong's, 4.2
    // times (9.6G), which this test fails (RACE-constant).
    let (n, rows) = split_bad_gor_both_ways(1024);
    let terms: Vec<(&[(usize, Int)], &Int)> = rows.iter().map(|(t, k)| (&t[..], k)).collect();
    scaling::compare_costs(
        "the race against Duong's search alone, BAD-GOR split both ways at k = 1,024",
        "the race should cost about twice the search that finishes first (RACE-constant)",
        3.5,
        || {
            std::hint::black_box(integer_empty_by(n, &terms, Search::Duong));
        },
        || {
            std::hint::black_box(integer_empty(n, &terms));
        },
    );
}

#[test]
fn split_bad_gor_scales() {
    // Measured in instructions from k = 128 to k = 1,024 (UTVPI-both-slow, load 58 to 68):
    // Goldberg and Radzik's search alone 32.7M to 1,694M (51.8 times), BF-Dijkstra alone 46.6M
    // to 2,826M (60.7 times), the two sharing labels 98.2M to 5,943M (60.5 times; sharing one
    // way only, 56 to 58 times), Duong's search alone 535M to 6,218M (11.6 times), and the race
    // of the pair and Duong's search 175M to 9,778M (55.9 times; 33.5 times the bytes). On
    // the reverse of the graph the pair is quick, and the race with a second pair searching
    // it takes 24.2M to 198M (8.2 times; COMPLEXITY.md C24).
    let (small, large) = (
        split_bad_gor(128, 1),
        split_bad_gor(scaling::FACTOR * 128, 1),
    );
    assert!(!raced(small.0, &small.1) && !raced(large.0, &large.1));
    scaling::check("BAD-GOR with its path split, by k", 128, |k| {
        let (n, rows) = if k == 128 { &small } else { &large };
        std::hint::black_box(raced(*n, rows));
    });
}

#[test]
fn bad_gor_and_a_fan_scale() {
    // BAD-GOR and the fan share no variable, so the split by strongly connected components
    // searches each alone, and each is slow for only one of the searches. Measured in
    // instructions from k = 256 to k = 2,048 (UTVPI-union): 36.1M to 301.2M, 8.3 times. The race
    // over the whole graph, before the split, took 202M to 12,236M (60.6 times; 48.8 times the
    // bytes in the negative control, run once and not committed), since both quadratic searches
    // are cheaper than Duong's below k = 2,048 (COMPLEXITY.md C24).
    let (small, large) = (
        bad_gor_and_fan(256, 0),
        bad_gor_and_fan(scaling::FACTOR * 256, 0),
    );
    assert!(!raced(small.0, &small.1) && !raced(large.0, &large.1));
    scaling::check("BAD-GOR augmented and a fan, by k", 256, |k| {
        let (n, rows) = if k == 256 { &small } else { &large };
        std::hint::black_box(raced(*n, rows));
    });
}

#[test]
fn bad_gor_and_a_fan_with_no_cycle_scale() {
    // The split by strongly connected components decides this graph in one pass in topological
    // order, since every component is one node; each of the three searches alone is slow on it.
    // Measured in instructions from k = 256 to k = 2,048: the split 5.29M to 42.3M (8.0 times);
    // Goldberg and Radzik's search 20.7M to 1,093M (52.8 times); BF-Dijkstra 44.6M to 2,891M
    // (64.8 times); Duong's search 573M to 6,203M (10.8 times, but the most work at both sizes).
    // Before UTVPI-union, the race without the pass took 141.3M to 9,142.5M (64.7 times). Since
    // UTVPI-union the race shares labels between its two quadratic searches, and without the
    // split it passes here, 20.1M to 166.4M (8.3 times), as does `the_acyclic_hub_scales` (the
    // control, run once and not committed); the split costs 8.4 times less than BF-Dijkstra
    // alone at k = 256, and 3.8 times less than the race without it.
    let (small, large) = (
        acyclic_bad_gor_and_fan(256),
        acyclic_bad_gor_and_fan(scaling::FACTOR * 256),
    );
    assert!(!empty(small.0, &small.1));
    scaling::check("BAD-GOR and a fan with no cycle, by k", 256, |k| {
        let (n, rows) = if k == 256 { &small } else { &large };
        std::hint::black_box(raced(*n, rows));
    });
}

#[test]
fn the_joined_union_family_scales() {
    // Joined and flipped, both slow halves lie in one strongly connected component: the split
    // by components leaves 459k to 25.9M units (56 times) to the old race. The race whose two
    // quadratic searches share labels takes 38.1M to 332.8M instructions (8.7 times). The old
    // code took 253M to 15,604M (47.6 times the bytes; negative control, not committed).
    let (small, large) = (
        union_family(256, true, true),
        union_family(scaling::FACTOR * 256, true, true),
    );
    assert!(!raced(small.0, &small.1) && !raced(large.0, &large.1));
    scaling::check("the joined union family, by k", 256, |k| {
        let (n, rows) = if k == 256 { &small } else { &large };
        std::hint::black_box(raced(*n, rows));
    });
}

#[test]
fn the_union_family_scales_through_decide() {
    decides(
        "the union family through decide, by k",
        256,
        Ok(true),
        |k| formula(&union_family(k, false, false).1),
    );
}

#[test]
fn the_joined_union_family_scales_through_decide() {
    // The old code took 618M to 18,351M instructions here (29.7 times). Unjoined, and joined by
    // a wide row, `decide` splits the halves into parts before the search and passed before too.
    decides(
        "the joined union family through decide, by k",
        256,
        Ok(true),
        |k| formula(&union_family(k, true, true).1),
    );
}

#[test]
fn the_wide_row_family_scales_through_decide() {
    decides(
        "the union family joined by a wide row, through decide, by k",
        256,
        Ok(true),
        wide_row_family,
    );
}

#[test]
fn coefficients_of_many_bits_scale() {
    // 64 variables, coefficients of 64 and of 512 bits: the work is linear in the bits, and
    // the answer is the same.
    let (small, large) = (tight_bits(64, 64), tight_bits(64, 512));
    for f in [&small, &large] {
        assert_eq!(decide(f), Err(Refusal::Growth));
    }
    scaling::check("the tight family by coefficient bits", 64, |b| {
        let f = if b == 64 { &small } else { &large };
        let _ = std::hint::black_box(decide(f));
    });
}

#[test]
fn columns_seen_through_two_aggregates_scale() {
    decides("two aggregates", 64, Ok(true), aggregates);
    let f = aggregates(64);
    let m = satisfiable(&f).expect("answered").expect("a point");
    assert!(f.holds(&m), "{m:?}");
}

#[test]
fn three_variables_in_many_rows_scale() {
    // The rows hold at (3, -2, 5). No elimination keeps them from growing and none of the
    // five points of the box meets every row, so `live3` decides them, in O(m log m). `x2` has
    // a unit coefficient in every row. With the `hull3` stage, which projected it out first,
    // the work grew 14.2 times from 64 to 512 rows, so the stage was removed (HULL3-subsumed).
    // At 64 rows `live3` finds the point in 6.7M instructions and 0.85 MB, a path the larger
    // sizes do not take, so the sizes are 128 and 1,024: 210M to 399M instructions, 8.3 MB to
    // 26.7 MB (512 to 4,096 rows: 392M to 454M, 22.2 MB to 56.4 MB). The cost depends on the
    // instance, not on its size: this seed takes 215M at 32 rows, 6.7M at 64 and 9.9M at 96, and
    // summed over 12 seeds 64 to 512 rows is 2.8 times the instructions and 4.7 the bytes
    // (HULL3-subsumed merge), so the ratio at 64 is that one cheap instance's.
    decides("three variables in many rows", 128, Ok(true), three_rows);
    let f = three_rows(64);
    let m = satisfiable(&f).expect("answered").expect("a point");
    assert!(f.holds(&m), "{m:?}");
}

#[test]
fn a_box_point_held_by_many_rows_scales() {
    // No elimination keeps these rows, so the box stage answers, and a point holds every row:
    // the stage reads each row once for each point it tries, which is linear in the rows.
    decides(
        "a box point held by many rows",
        256,
        Ok(true),
        rows_held_in_a_box,
    );
}
