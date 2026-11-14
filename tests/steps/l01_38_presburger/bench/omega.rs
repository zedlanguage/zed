//! The benchmarks of `omega.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::omega::*;
use zed_tests::scaling;
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::presburger::{Atom, Formula, project_each, row_box, satisfiable};

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
            let m = satisfiable(f).unwrap().expect("a point");
            assert!(f.holds(&m));
            let digits = m.values().map(|v| v.to_string().len()).max().unwrap();
            assert!(digits <= n * scaling::FACTOR, "{digits} digits");
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
        let m = satisfiable(f).unwrap().expect("a point");
        assert!(f.holds(&m), "{m:?}");
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
    let n = 1800;
    let (small, large) = (bounded_sum(n), bounded_sum(scaling::FACTOR * n));
    let syms = |m: usize| -> Vec<Atom> { (0..m).map(|i| sym(&format!("x{i}"))).collect() };
    let (s_small, s_large) = (syms(n), syms(scaling::FACTOR * n));
    let want = IntervalSet::range(End::Fin(Num::from(0)), End::Fin(Num::from(49)));
    for (f, s) in [(&small, &s_small), (&large, &s_large)] {
        assert!(row_box(f, s).iter().all(|b| *b == want));
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
fn a_value_between_a_long_sum_and_many_bounds_is_not_eliminated_first() {
    // Every b[j] and c[i] is pulled to its bound; `a` then has two bounds of its own, and its
    // elimination, n rows of n terms, is never taken.
    let n = 280;
    let (small, large) = (fed_sum(n), fed_sum(scaling::FACTOR * n));
    for f in [&small, &large] {
        let m = satisfiable(f).unwrap().expect("a point");
        assert!(f.holds(&m), "{m:?}");
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
        let m = satisfiable(f).unwrap().expect("a point");
        assert!(f.holds(&m), "{m:?}");
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
            dead2(470, chain, "z"),
            dead2(470 * scaling::FACTOR, chain, "z"),
        );
        let (s_small, s_large) = (
            [sym("z0"), sym("z15")],
            [sym("z0"), sym(&format!("z{}", 470 * scaling::FACTOR - 1))],
        );
        scaling::check_order(
            &format!("the first and last credits of a pipeline of stages, chained {chain}"),
            470,
            1,
            |n| {
                let (f, s) = if n == 470 {
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
    let inputs = scaling::inputs(890, |n| (dead2(n, false, "z"), syms(n)));
    scaling::check_order(
        "every state and credit of a pipeline of stages",
        890,
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
    let inputs = scaling::inputs(450, |n| (joint_stages(n), joint_syms(n)));
    scaling::check_order("every symbol of stages that share no atom", 450, 1, |n| {
        let (f, s) = &inputs[&n];
        let _ = std::hint::black_box(project_each(f, s));
    });
}

/// Projecting the first credit of a chained pipeline of `n` stages costs O(n log n): each
/// choice is tested against the rows projected onto its own stage, not against the whole
/// chain, which cost `n` solves of `n` rows before (40.6 times the instructions from 16 to
/// 128 stages).
#[test]
fn project_each_on_a_chained_pipeline_scales() {
    let (small, large) = (
        dead2(990, true, "z"),
        dead2(990 * scaling::FACTOR, true, "z"),
    );
    let syms = [sym("z0")];
    scaling::check_order(
        "the first credit of a chained pipeline of stages",
        990,
        1,
        |n| {
            let f = if n == 990 { &small } else { &large };
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
    let n = 180;
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
