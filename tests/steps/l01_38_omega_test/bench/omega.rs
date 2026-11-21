//! The benchmarks of `omega.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::omega::*;
use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::presburger::{
    Atom, Con, Formula, Lin, decide, project_each, row_box, satisfiable,
};

#[test]
fn chains_of_equalities_cost_the_digits_of_their_values() {
    // n values of n digits each: the output itself is quadratic in bits, and the work is too.
    // Control: T4 took 297 times as long from 64 to 512 and over 30 s at 1024.
    for (name, build) in [
        ("3x + 5y == 7", euclid_chain as fn(usize) -> Formula),
        ("6x + 10y + 15z == 7", euclid_chain3),
    ] {
        let n = 490;
        let (small, large) = (build(n), build(scaling::FACTOR * n));
        for f in [&small, &large] {
            assert_a_point_of_few_digits(f, n);
        }
        scaling::check_order(name, n, 2, |m| {
            drop(satisfiable(if m == n { &small } else { &large }));
        });
    }
}

#[test]
fn equalities_substituted_into_a_long_row_cost_the_row_each_time() {
    // The equalities are solved among themselves, and the row is rewritten once for all of them.
    // Control: T4 took 121 times as long.
    let n = 1200;
    let (small, large) = (tied_sum(n), tied_sum(scaling::FACTOR * n));
    for f in [&small, &large] {
        assert!(satisfiable(f).unwrap().is_some());
    }
    scaling::check_order("a long row with equalities", n, 1, |m| {
        drop(satisfiable(if m == n { &small } else { &large }));
    });
}

#[test]
fn eliminating_the_terms_of_a_long_row_costs_the_row_each_time() {
    // Every x[i] is pulled to its lower bound by the one long row, and all are fixed there at
    // once, the row written once. Control: T4 took 38 times as long.
    let n = 1400;
    let (small, large) = (bounded_sum(n), bounded_sum(scaling::FACTOR * n));
    for f in [&small, &large] {
        assert_a_point_holds(f);
    }
    scaling::check_order("a sum of bounded terms", n, 1, |m| {
        drop(satisfiable(if m == n { &small } else { &large }));
    });
}

/// The bounds the box stage gives the rows of a refused projection cost O(T log T) in the T
/// terms: each row tightens each of its terms from one sum of the bounds of the others, not from
/// a new sum for each term. `bounded_sum` gives each `x[i]` in [0, 49].
#[test]
fn the_box_of_refused_rows_scales() {
    let n = 1400;
    let (small, large) = (bounded_sum(n), bounded_sum(scaling::FACTOR * n));
    let (s_small, s_large) = (bounded_sum_syms(n), bounded_sum_syms(scaling::FACTOR * n));
    for (f, s) in [(&small, &s_small), (&large, &s_large)] {
        assert_each_count_in_its_budget(f, s);
    }
    scaling::check_order("the box of one long row", n, 1, |m| {
        drop(if m == n {
            row_box(&small, &s_small)
        } else {
            row_box(&large, &s_large)
        });
    });
}

#[test]
fn eliminations_that_each_rewrite_one_long_row_scale() {
    // Each p[i] has one row on each side, one of them the long row, and once it is eliminated
    // y[i] is fixed into the long row (FAIL-open-sides-bench-ratio: the products of
    // `products_whose_factors_keep_open_sides_scale` in the long row of the negated goal).
    let n = 200;
    let (small, large) = (linked_sum(n), linked_sum(scaling::FACTOR * n));
    for f in [&small, &large] {
        assert_eq!(satisfiable(f), Ok(None));
    }
    scaling::check_order("eliminations that each rewrite one long row", n, 1, |m| {
        drop(satisfiable(if m == n { &small } else { &large }));
    });
}

#[test]
fn bounds_that_each_fix_one_term_of_a_long_row_scale() {
    // Each elimination of a w[i] leaves z[i] at one bound, which the long row pulls it to
    // (FAIL-open-sides-bench-ratio: the factors of the second linear reading of
    // `products_whose_factors_keep_open_sides_scale`).
    let n = 200;
    let (small, large) = (fixed_sum(n), fixed_sum(scaling::FACTOR * n));
    for f in [&small, &large] {
        assert_eq!(satisfiable(f), Ok(None));
    }
    scaling::check_order("bounds that each fix one term of a long row", n, 1, |m| {
        drop(satisfiable(if m == n { &small } else { &large }));
    });
}

#[test]
fn a_value_between_a_long_sum_and_many_bounds_is_not_eliminated_first() {
    // Every b[j] and c[i] is pulled to its bound; `a` then has two bounds of its own, and its
    // elimination, n rows of n terms, is never taken.
    let n = 280;
    let (small, large) = (fed_sum(n), fed_sum(scaling::FACTOR * n));
    for f in [&small, &large] {
        assert_a_point_holds(f);
    }
    scaling::check_order("a value below a sum", n, 1, |m| {
        drop(satisfiable(if m == n { &small } else { &large }));
    });
}

#[test]
fn a_value_that_alone_removes_a_row_is_eliminated_first_at_cubic_cost() {
    // Eliminating `a` first would write n rows of n terms, which is fill, and the variables with
    // no fill go first. Control: T4 took 90 times as long, and was held at cubic.
    let n = 850;
    let (small, large) = (tied_fed_sum(n), tied_fed_sum(scaling::FACTOR * n));
    for f in [&small, &large] {
        assert_a_point_holds(f);
    }
    scaling::check_order("a value below a tied sum", n, 1, |m| {
        drop(satisfiable(if m == n { &small } else { &large }));
    });
}

/// Projecting the first and the last credit of a pipeline of `n` stages costs O(n log n),
/// chained or not (stages not chained are alike, so they are projected as sets): the stalls
/// are removed by the values of each state, one pass over the disjuncts' ranges, and each
/// credit's hull is then `[0..=5]` (item PROJECT-hull-credit-lower).
#[test]
fn the_first_and_last_credits_of_a_pipeline_scale() {
    for chain in [false, true] {
        let (small, large) = (
            dead2(300, chain, "z"),
            dead2(300 * scaling::FACTOR, chain, "z"),
        );
        let (s_small, s_large) = (
            [sym("z0"), sym("z15")],
            [sym("z0"), sym(&format!("z{}", 300 * scaling::FACTOR - 1))],
        );
        scaling::check_order(
            &format!("the first and last credits of a pipeline of stages, chained {chain}"),
            300,
            1,
            |n| {
                let (f, s) = if n == 300 {
                    (&small, &s_small)
                } else {
                    (&large, &s_large)
                };
                let _ = std::hint::black_box(zedc::store::presburger::project_each(f, s));
            },
        );
    }
}

/// Projecting every state and credit of an unchained pipeline of `n` stages costs
/// O(n log n): each hull is tightened over its own stage, not the whole formula, which cost
/// O(n) per symbol before, 56.1 times the bytes from 16 to 128 stages (item
/// TIGHTEN-each-whole). The chained pipeline is left out: its tightening is now O(n log n),
/// but each disjunct is still projected onto every symbol of the chain, O(n) per disjunction
/// (item PROJECT-each-chain-all).
#[test]
fn every_state_and_credit_of_a_pipeline_scale() {
    let syms = |n: usize| -> Vec<Atom> {
        (0..n)
            .flat_map(|k| [sym(&format!("z{k}")), sym(&format!("y{k}"))])
            .collect()
    };
    let inputs = scaling::inputs(690, |n| (dead2(n, false, "z"), syms(n)));
    scaling::check_order(
        "every state and credit of a pipeline of stages",
        690,
        1,
        |n| {
            let (f, s) = &inputs[&n];
            let _ = std::hint::black_box(zedc::store::presburger::project_each(f, s));
        },
    );
}

/// Projecting every symbol of [`joint_stages`] of `n` stages costs O(n log n): each end is
/// asked of its own stage, not of the whole formula, which cost O(n) per question and O(n²)
/// in all before (item TIGHTEN-each-whole).
#[test]
fn independent_stages_scale() {
    let inputs = scaling::inputs(225, |n| (joint_stages(n), joint_syms(n)));
    scaling::check_order("every symbol of stages that share no atom", 225, 1, |n| {
        let (f, s) = &inputs[&n];
        let _ = std::hint::black_box(project_each(f, s));
    });
}

/// Projecting the first credit of a chained pipeline of `n` stages costs O(n log n): each
/// choice is tested against the rows projected onto its own stage, not against the whole
/// chain, which cost `n` solves of `n` rows before (40.6 times the instructions from 16 to
/// 128 stages).
///
/// The ratio is above the goal of 9 by the log factor of the halving, so it is held to the
/// predicted ratio of standing rule P300, 8·ln(8n)/ln(n) = 10.70 at n = 470 (row
/// PERF-dead2-chained-ratio). Proof: `settle_as_sets` runs `by_halves` once over the n + 1
/// stage sets of the chain, and `project_parts` once more over its levels. A range of w items
/// is projected from its parent's rows, which after the parent's projection lie on the parent's
/// items and the rows that link them, O(w) rows; the ranges of one depth cover the k items
/// once, so each depth projects O(k) rows, and there are ⌈log₂ k⌉ depths: O(k log k) rows
/// projected in all. Each projection is linear in its rows: `linked_to` visits each row and
/// atom once, and `shadow` eliminates each chain atom once, reading and making O(1) rows, and
/// each hash lookup is O(1) expected. The O(1) rows (PROOF-dead2-shadow-constant): the rows
/// are bounds of one atom and chain rows `y[j] - y[i] + c >= 0` between two states, every
/// coefficient ±1. Invariant: each state `y` left holds at most one bound of each sign
/// (`shadow` keeps the tighter of two rows on one form) and at most two chain rows, one to
/// the nearest state left on each side, with `y` of sign +1 toward the earlier stage and -1
/// toward the later; a credit holds only its bounds. Eliminating `y[k]` pairs its at most two
/// lower bounds (its own and the chain row to the earlier state) with its at most two upper
/// bounds, at most 4 pairs, each making a bound of a neighbor (kept or dropped by the tighter)
/// or the one chain row between the two neighbors, which is again of that shape, so the
/// invariant holds after it; a credit's elimination makes a row without atoms. So each
/// elimination reads at most 4 rows and makes at most 4, at every n. Tested by the probe of
/// `presburger::by_halves_against_old::dead2_eliminations_read_as_many_rows_at_every_length`
/// (in the crate, which counts the most rows taken and pairs made by one elimination): (4, 4) at
/// 16 and at 128 stages, every symbol asked or the first credit alone. Measured, the rows projected
/// go from 16,761 to 179,120 (10.69 times) and the instructions 9.6 times (857 M → 8.26 G).
#[test]
fn project_each_on_a_chained_pipeline_scales() {
    let (small, large) = (
        dead2(470, true, "z"),
        dead2(470 * scaling::FACTOR, true, "z"),
    );
    let syms = [sym("z0")];
    scaling::check_order(
        "the first credit of a chained pipeline of stages",
        470,
        1,
        |n| {
            let f = if n == 470 { &small } else { &large };
            let _ = std::hint::black_box(zedc::store::presburger::project_each(f, &syms));
        },
    );
}

#[test]
fn twin_definitions_merge_in_time_near_linear() {
    // n pairs of twins over the same symbol: numbering the definitions is one pass in the order
    // of their dependencies with a hash lookup each, and the merged formula has n absolute
    // values of one symbol. Control (once, not kept): an O(n²) scan of the definitions in the
    // merge failed this test.
    let n = 85;
    let (small, large) = (
        twin_absolute_values(n),
        twin_absolute_values(scaling::FACTOR * n),
    );
    for (m, f) in [(n, &small), (scaling::FACTOR * n, &large)] {
        let (each, _) = project_each(f, &[sym("i")]).expect("answered");
        let m = m as i64;
        let want = [
            (End::NegInf, End::Fin(Num::from(-3))),
            (End::Fin(Num::from(m + 2)), End::Fin(Num::from(m + 10))),
        ];
        assert_eq!(
            each[0].clone().expect("answered"),
            IntervalSet::from_pieces(want.to_vec()),
            "{m}"
        );
    }
    scaling::check_order(
        "twin definitions merged before a tied projection",
        n,
        1,
        |m| {
            drop(project_each(
                if m == n { &small } else { &large },
                &[sym("i")],
            ));
        },
    );
}

// The 2000 formulas of seed 0x1380 reordered, in four quarters of one sequence, each under the
// 20-second limit of a piece: many cases, so benchmarks (author P178). 40 of a new seed run in
// `omega::the_answer_does_not_depend_on_the_order_of_the_disjuncts`.

/// Quarter `q` of the 2000 formulas: more than half of its 500 are changed by the reordering.
fn reordered_quarter(q: usize) {
    let mut rng = Rng::new(0x1380);
    let disjunctive = reordered_formulas_agree(&mut rng, 500 * q, 500 * (q + 1));
    assert!(disjunctive > 250, "{disjunctive} of 500 reordered");
}

#[test]
fn the_answer_does_not_depend_on_the_order_of_the_disjuncts_in_a_first_quarter() {
    reordered_quarter(0);
}

#[test]
fn the_answer_does_not_depend_on_the_order_of_the_disjuncts_in_a_second_quarter() {
    reordered_quarter(1);
}

#[test]
fn the_answer_does_not_depend_on_the_order_of_the_disjuncts_in_a_third_quarter() {
    reordered_quarter(2);
}

#[test]
fn the_answer_does_not_depend_on_the_order_of_the_disjuncts_in_a_fourth_quarter() {
    reordered_quarter(3);
}

/// The 60 writings of seed 0x236 of `omega::case_236_in_writings`; six of a new seed run in
/// `omega::a_disjunct_with_no_point_beside_a_point_gives_one_answer_in_every_writing`.
#[test]
fn a_disjunct_with_no_point_beside_a_point_gives_one_answer_in_60_writings() {
    case_236_in_writings(&mut Rng::new(0x236), 60);
}

#[test]
fn factors_defined_alike_merge_in_time_near_linear() {
    // n copies of a tied decision left unsettled by the search by colors: the merge of the
    // atoms defined alike is one pass in the order of their dependencies with a hash lookup
    // each, plus one pass over the products, and the merged formula is decided once.
    let n = 40;
    let (small, large) = (
        tied_factor_blocks(n),
        tied_factor_blocks(scaling::FACTOR * n),
    );
    for f in [&small, &large] {
        assert_eq!(decide(f).ok(), Some(true), "{f}");
    }
    scaling::check_order(
        "factors defined alike merged before a tied decision",
        n,
        1,
        |m| {
            drop(decide(if m == n { &small } else { &large }));
        },
    );
}

/// `n` copies of the formula of seed 12037625683208242449 (FAIL-presburger-fresh-seed-refusals),
/// copy `c` over `q{c}_0` to `q{c}_4`, with `q{c+1}_0 <= q{c}_4`: one system with a point (each
/// copy at q0 = 2, q1 = 3, q2 = 3, q3 = -2, q4 = 4), as `seed_12037625683208242449_chain` in
/// zedc-presburger builds it, whose test checks that each copy takes the lossless stage of the
/// Omega test.
fn chained_seeds(n: usize) -> Formula {
    let mut rows = Vec::new();
    for c in 0..n {
        let q = |i: usize| format!("q{c:06}_{i}");
        let ge2 = |a: &[(usize, i128)], k: i128| {
            let names: Vec<(String, i128)> = a.iter().map(|(i, x)| (q(*i), *x)).collect();
            let terms: Vec<(&str, i128)> = names.iter().map(|(s, x)| (s.as_str(), *x)).collect();
            ge_rows(&terms, k)
        };
        rows.extend([
            ge2(&[(0, 1)], -2),
            ge2(&[(0, -1)], 3),
            ge2(&[(1, 2), (0, -3)], 0),
            ge2(&[(0, 3), (1, -2)], 1),
            ge2(&[(2, 3)], -1),
            ge2(&[(2, 2), (3, 2)], -1),
            ge2(&[(2, -2), (3, -2)], 3),
            ge2(&[(3, 3), (4, 2)], -1),
            ge2(&[(3, -3), (4, -2)], 2),
            ge2(&[(4, 1), (0, -1)], -1),
        ]);
        if c + 1 < n {
            let next = format!("q{:06}_0", c + 1);
            rows.push(ge_rows(&[(q(4).as_str(), 1), (next.as_str(), -1)], 0));
        }
    }
    Formula::and(rows)
}

/// `Σ c·s + k >= 0`.
fn ge_rows(terms: &[(&str, i128)], k: i128) -> Formula {
    let lin = terms.iter().fold(Lin::constant(k), |l, (s, c)| {
        l.plus(&Lin::atom(Atom::Sym(s.to_string().into())).times(*c))
    });
    Formula::Con(Con::ge(&lin, &Lin::constant(0)))
}

/// The lossless stage of the Omega test (FAIL-presburger-fresh-seed-refusals,
/// `System::renew_lossless`): each step reads the pairs of the variables whose rows changed,
/// O(T log T) for their T terms, so on [`chained_seeds`], whose copies each change a fixed
/// number of rows a step, the whole run is near linear. COMPLEXITY.md row LOSSLESS-pairs.
#[test]
fn lossless_bands_scale() {
    let n = 1000;
    let (small, large) = (chained_seeds(n), chained_seeds(scaling::FACTOR * n));
    for f in [&small, &large] {
        assert_eq!(decide(f), Ok(true), "{f}");
    }
    scaling::check_order("chained bands with lossless pairs", n, 1, |m| {
        drop(decide(if m == n { &small } else { &large }));
    });
}
