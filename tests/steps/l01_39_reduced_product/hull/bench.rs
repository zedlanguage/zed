//! Benchmarks of `hull`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

#[test]
fn a_join_costs_near_the_rows_that_differ() {
    // n joins of hulls of n rows differing in one, whose pivot sorts before every other: near
    // n log n in all.
    let hulls: BTreeMap<usize, Hull> = [N_JOIN, scaling::FACTOR * N_JOIN]
        .into_iter()
        .map(|m| (m, rows_of(m)))
        .collect();
    scaling::check("the join of hulls", N_JOIN, |m| {
        loop_joins(&hulls[&m], m, |i| format!("x{i}"))
    });
}

#[test]
fn a_join_costs_near_the_rows_that_differ_wherever_they_sort() {
    // As above, with the new row's pivot among the rows' pivots `y…` (`y12a` sorts between
    // `y12` and `y120`) and after all of them.
    let hulls: BTreeMap<usize, Hull> = [N_JOIN, scaling::FACTOR * N_JOIN]
        .into_iter()
        .map(|m| (m, rows_of(m)))
        .collect();
    scaling::check("the join of hulls, a row among the others", N_JOIN, |m| {
        loop_joins(&hulls[&m], m, |i| format!("y{i}a"))
    });
    scaling::check("the join of hulls, a row after the others", N_JOIN, |m| {
        loop_joins(&hulls[&m], m, |i| format!("zz{i}"))
    });
}

#[test]
fn a_hull_is_built_row_by_row_in_time_near_its_rows() {
    // Each row is added to a hull that no one else holds, so it is changed in place.
    let rows: BTreeMap<usize, Vec<Lin>> = [N_BUILD, scaling::FACTOR * N_BUILD]
        .into_iter()
        .map(|m| (m, star(m)))
        .collect();
    scaling::check("building a hull row by row", N_BUILD, |m| {
        let h = Hull::of(&rows[&m]);
        assert_eq!(h.rows().count(), m + 1);
    });
}

/// The sizes, set so the 1x case runs about 0.3 s (TEST-bench-move-l0139; were 256 and 512).
const N_JOIN: usize = 16_384;
const N_BUILD: usize = 65_536;
