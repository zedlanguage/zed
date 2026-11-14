//! The benchmarks of `one_row.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::one_row::*;
use zed_tests::scaling;
use zedc::store::interval::IntervalSet;
use zedc::store::presburger::{Formula, decide, project_each, satisfiable};

#[test]
fn a_box_and_one_row_scale() {
    let k = 470;
    let (small, large) = (dense(k), dense(scaling::FACTOR * k));
    let (ys, yl) = (names(k), names(scaling::FACTOR * k));
    for f in [&small, &large] {
        assert_eq!(decide(f), Ok(true));
    }
    scaling::check_order("decide: a box and one row", k, 1, |m| {
        drop(decide(if m == k { &small } else { &large }));
    });
    scaling::check_order("project_each: a box and one row", k, 1, |m| {
        drop(if m == k {
            project_each(&small, &ys)
        } else {
            project_each(&large, &yl)
        });
    });
}

#[test]
fn residue_and_ends_of_a_row_scale() {
    let k = 490;
    for (name, build, answer) in [
        (
            "target zero",
            (|k| choice_sum(&weights(k), 0)) as fn(usize) -> Formula,
            true,
        ),
        ("even weights, odd target", parity, false),
    ] {
        let (small, large) = (build(k), build(scaling::FACTOR * k));
        let (ys, yl) = (names(k), names(scaling::FACTOR * k));
        for f in [&small, &large] {
            assert_eq!(decide(f), Ok(answer), "{name}");
        }
        scaling::check_order(&format!("decide: {name}"), k, 1, |m| {
            drop(decide(if m == k { &small } else { &large }));
        });
        scaling::check_order(&format!("project_each: {name}"), k, 1, |m| {
            drop(if m == k {
                project_each(&small, &ys)
            } else {
                project_each(&large, &yl)
            });
        });
    }
}

#[test]
fn a_forced_contradiction_projects_to_empty_in_linear_work() {
    scaling::check_order(
        "paired chain projection via forced contradiction",
        16000,
        1,
        |k| {
            let f = paired_chain(k, false);
            let (each, skipped) = project_each(&f, &[sym("y0")]).unwrap();
            assert_eq!(each, vec![Ok(IntervalSet::empty())]);
            assert!(skipped.is_empty());
        },
    );
}

/// `satisfiable` on a box and one row, and on subset sums with target 0, at `n = 64` and
/// `8n = 512`; the point each gives is checked by `holds` outside the measured runs.
#[test]
fn satisfiable_on_a_box_and_one_row_scales() {
    let k = 800;
    let large = scaling::FACTOR * k;
    for (name, small, large) in [
        ("a box and one row", dense(k), dense(large)),
        (
            "subset sums to 0",
            choice_sum(&weights(k), 0),
            choice_sum(&weights(large), 0),
        ),
    ] {
        for f in [&small, &large] {
            let m = satisfiable(f).expect("an answer").expect("a point");
            assert!(f.holds(&m), "{name}: {m:?}");
        }
        scaling::check_order(&format!("satisfiable: {name}"), k, 1, |m| {
            drop(satisfiable(if m == k { &small } else { &large }));
        });
    }
}

/// I19: public model construction uses the same exact class as public decision. Checking
/// the certificate is outside the measured closure, so a cheap holds cannot hide slow search.
#[test]
fn a_box_and_an_extreme_row_build_their_models_in_near_linear_work() {
    for (what, build) in [
        ("dense model", dense as fn(usize) -> Formula),
        (
            "zero model",
            (|k| choice_sum(&weights(k), 0)) as fn(usize) -> Formula,
        ),
    ] {
        let (small, large) = (build(750), build(6000));
        for f in [&small, &large] {
            assert!(f.holds(&satisfiable(f).unwrap().unwrap()));
        }
        scaling::check_order(what, 750, 1, |k| {
            drop(satisfiable(if k == 750 { &small } else { &large }));
        });
    }
}
