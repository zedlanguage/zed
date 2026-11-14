//! The benchmarks of `scaling.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::scaling::*;
use std::sync::Arc;
use zed_tests::scaling;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Refusal, decide, satisfiable};

#[test]
fn a_chain_of_inexact_eliminations_with_a_point_scales() {
    scales("the chain with a point", 1900, true, |v| chain(v, 3));
}

#[test]
fn an_empty_chain_scales() {
    scales("the empty chain", 4000, false, |v| chain(v, 0));
}

#[test]
fn a_rising_chain_scales() {
    scales("the rising chain", 2800, false, rising);
}

/// OMEGA-cycle-growth: the cycle's equalities are found as strongly connected components, in
/// O(m log m), before any elimination.
#[test]
fn a_cycle_of_rows_scales() {
    scales("a cycle of rows", 870, false, cycle);
}

#[test]
fn a_long_chain_with_a_point_scales() {
    scales("the long chain with a point", 3000, true, |v| chain(v, 3));
}

#[test]
fn a_long_empty_chain_scales() {
    scales("the long empty chain", 5100, false, |v| chain(v, 0));
}

#[test]
fn a_long_rising_chain_scales() {
    scales("the long rising chain", 4000, false, rising);
}

#[test]
fn the_shifted_sparse_family_scales() {
    decides(
        "the shifted sparse family",
        1200,
        Err(Refusal::Growth),
        sparse,
    );
}

#[test]
fn rows_of_two_unit_coefficients_scale() {
    decides("rows of two unit coefficients", 13000, Ok(true), utvpi);
}

#[test]
fn an_odd_cycle_scales() {
    decides("an odd cycle", 11000, Ok(false), odd_cycle);
}

#[test]
fn disjoint_two_variable_parts_scale() {
    decides(
        "disjoint copies of Pugh's example",
        1900,
        Ok(false),
        pugh_pairs,
    );
}

#[test]
fn a_chain_into_a_refused_block_scales() {
    decides(
        "a chain into a refused block",
        2800,
        Err(Refusal::Growth),
        chain_into_block,
    );
}

#[test]
fn random_rows_of_two_unit_coefficients_scale() {
    decides(
        "random rows of two unit coefficients",
        3900,
        Ok(true),
        |n| random_unit_rows(n, 4 * n, 0xabc),
    );
}

#[test]
fn pughs_example_in_a_chain_scales() {
    decides(
        "Pugh's example in a chain",
        530,
        Err(Refusal::Shadows),
        pugh_in_a_chain,
    );
}

#[test]
fn the_box_stage_with_a_hub_in_one_row_per_block_scales() {
    // HUB-SCALE: the row test of the box stage (Q1-ROWBOX) is one pass over the terms, so a
    // hub in a row of every block costs nothing per row beyond its own term. Measured
    // 2026-11-03: 9.1 times the instructions from 16 to 128 and 9.3 from 64 to 512; with
    // `row_box_empty` run again over every row of each variable of a row it was 44.6 and
    // 175.2, and with the bounds rebuilt for each row from the rows before it, 32.8 and 49.6.
    decides(
        "the box stage with a hub in one row per block",
        620,
        Err(Refusal::Growth),
        |n| rows_of(&blocks_with_a_hub(n)),
    );
}

#[test]
fn the_row_test_of_the_box_scales() {
    // Measured 2026-11-03: 8.7 times the instructions from 16 to 128 and 9.2 from 64 to 512;
    // 46.5 and 209.5 with `row_box_empty` run again over every row of each variable of a row.
    // With the bounds rebuilt for each row it was 12.4 and 21.3, under the limit, since the
    // crossing is found early; the hub family above shows that cost.
    decides(
        "the row test of the box with a crossing after the hub's blocks",
        670,
        Ok(false),
        |n| rows_of(&blocks_with_a_hub_and_a_crossing(n)),
    );
}

#[test]
fn all_ordered_pairs_of_differences_scale() {
    scales_by_rows(
        "all ordered pairs of differences",
        (12, 33),
        |v| v * (v - 1),
        all_pairs,
    );
}

#[test]
fn a_grid_of_differences_scales() {
    scales_by_rows("a grid of differences", (12, 33), |v| 4 * v * (v - 1), grid);
}

#[test]
fn sorted_indices_under_a_symbolic_length_scale() {
    scales("sorted indices", 17000, true, |v| sorted(v, false));
}

#[test]
fn overlapping_sums_of_three_scale() {
    scales("overlapping sums of three", 18000, true, sums);
}

#[test]
fn a_grid_of_differences_is_decided_in_scale() {
    let (small, large) = (grid(117), grid(330));
    for f in [&small, &large] {
        assert_eq!(decide(f), Ok(true), "a grid of differences");
    }
    scaling::check("deciding a grid of differences (rows)", 54288, |m| {
        let _ = std::hint::black_box(decide(if m == 54288 { &small } else { &large }));
    });
}

/// The point of a grid of 33 and of 93 names, 4224 and 34224 rows (8.1 times). Until
/// UTVPI-model, once `utvpi::integer_empty` had shown a point, `Omega::run` placed it by
/// eliminating every variable with fill allowed, and this took 31.1 times the instructions
/// (2026-11-05); the point is now rounded from a potential (`utvpi::integer_point`).
/// COMPLEXITY.md S38.
#[test]
fn the_point_of_a_larger_grid_of_differences_scales() {
    let (small, large) = (grid(33), grid(93));
    point_of("a grid of 33", &small);
    point_of("a grid of 93", &large);
    scaling::compare(
        "the point of a grid of differences: 4224 and 34224 rows, 8.1 times",
        1,
        || drop(satisfiable(&small)),
        || drop(satisfiable(&large)),
    );
}

/// The point of `expander`'s rows at 256 and 2048 variables, checked against each row
/// (UTVPI-model). Before, placing it eliminated with fill allowed: 277M to 1,500M instructions
/// from 128 to 256 variables (cross-review xt2, note3b.tsv).
#[test]
fn the_point_of_an_expander_of_differences_scales() {
    let (small, large) = (expander(980), expander(scaling::FACTOR * 980));
    point_of("an expander of differences", &small);
    point_of("an expander of differences", &large);
    scaling::check("the point of an expander of differences", 980, |m| {
        drop(satisfiable(if m == 980 { &small } else { &large }));
    });
}

#[test]
fn splinters_of_splinters_scale() {
    decides("copies split twice", 94, Ok(true), split_twice_copies);
    decides(
        "a chain into a block split twice",
        1600,
        Ok(true),
        split_twice_in_a_chain,
    );
}

/// k bounds `ai >= 0` added one at a time, each to a copy of the conjunction before, beside one
/// constraint on a term of k names, `z0 + ... + z(k-1) >= 0`. Its term is the greatest key of
/// the map of the constraints kept on each term (`Conjuncts::tight`), and the names are numbered
/// so that each new key is greater than the last, so each lands in the leaf that holds the wide
/// term, and the copy copies that leaf. A key held by value cost its k names at each copy, O(k)
/// a bound and O(k^2) in all; shared, O(1) a bound (item PERF-conjuncts-term-keys, COMPLEXITY.md
/// C46). Likewise k disjunctions `ai >= 0 || bi >= 0` beside `z0 + ... + z(k-1) >= 0 || y >= 0`,
/// for the map of the disjunctions of two constraints by their two terms (`Conjuncts::pair`).
#[test]
fn a_conjunct_beside_a_wide_one_costs_its_own_key() {
    let wide = |k: usize| {
        let sum = (0..k).fold(Lin::constant(0), |l, i| {
            l.plus(&Lin::atom(Atom::Sym(Arc::from(format!("z{i:06}")))))
        });
        Formula::Con(Con::ge(&sum, &Lin::constant(0)))
    };
    let bounds = scaling::inputs(730, |k| {
        let small: Vec<Formula> = (0..k).map(|i| at_least_zero(&format!("a{i:06}"))).collect();
        (wide(k), small)
    });
    scaling::check("bounds beside a constraint on k names", 730, |k| {
        let (wide, small) = &bounds[&k];
        std::hint::black_box(each_on_a_copy(wide, small));
    });
    let pairs = scaling::inputs(730, |k| {
        let small: Vec<Formula> = (0..k)
            .map(|i| {
                Formula::or(vec![
                    at_least_zero(&format!("a{i:06}")),
                    at_least_zero(&format!("b{i:06}")),
                ])
            })
            .collect();
        (Formula::or(vec![wide(k), at_least_zero("y")]), small)
    });
    scaling::check(
        "disjunctions of two bounds beside one of a constraint on k names",
        730,
        |k| {
            let (wide, small) = &pairs[&k];
            std::hint::black_box(each_on_a_copy(wide, small));
        },
    );
}
