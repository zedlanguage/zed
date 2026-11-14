//! The benchmarks of `names.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::names::*;
use zed_tests::scaling;
use zedc::store::presburger::{Atom, decide, project_each, satisfiable};

#[test]
fn decide_scales_over_copies_of_a_tie() {
    // Each copy of the five-variable counterexample is refused with a tie.
    scales_over_copies("copies of a tie", &claude5(), 5, 72);
}

#[test]
fn decide_scales_over_copies_of_a_system_with_tied_variables() {
    // Each copy of Codex's six-variable system, whose variables tie, has a point.
    scales_over_copies("copies of Codex's system", &codex6(), 6, 58);
}

#[test]
fn decide_scales_over_copies_of_tied_equalities() {
    // Each copy of `x + y == 5`, `x, y >= 0` keeps its equality as rows and has a point.
    let rows = vec![eq(&[1, 1], -5), ge(&[1, 0], 0), ge(&[0, 1], 0)];
    scales_over_copies("copies of tied equalities", &rows, 2, 180);
}

#[test]
fn decide_scales_over_one_class_of_equalities() {
    // `Ties` joins every equality of the class, and `representatives` reads each variable's
    // root once; with union by rank both cost a logarithm per variable.
    let (small, large) = (
        one_class_of_equalities(48000),
        one_class_of_equalities(48000 * scaling::FACTOR),
    );
    assert_eq!((decide(&small), decide(&large)), (Ok(true), Ok(true)));
    scaling::check_order("decide on one class of equalities", 48000, 1, |n| {
        let f = if n == 48000 { &small } else { &large };
        let _ = std::hint::black_box(decide(f));
    });
}

#[test]
fn decide_scales_over_one_system_with_many_tied_variables() {
    // One connected system, unlike the copies above, so the cost of choosing the tied leaves
    // at each step is read, not that of splitting the system into parts.
    let (small, large) = (star(19000), star(19000 * scaling::FACTOR));
    assert_eq!((decide(&small), decide(&large)), (Ok(true), Ok(true)));
    scaling::check_order("decide on a star of tied leaves", 19000, 1, |n| {
        let f = if n == 19000 { &small } else { &large };
        let _ = std::hint::black_box(decide(f));
    });
}

#[test]
fn decide_scales_over_a_renamed_chain_with_disjunctions() {
    let (small, large) = (
        chain_with_disjunctions(500, 500),
        chain_with_disjunctions(500 * scaling::FACTOR, 500 * scaling::FACTOR),
    );
    assert_eq!((decide(&small), decide(&large)), (Ok(true), Ok(true)));
    scaling::check("decide on a chain with disjunctions", 500, |n| {
        let f = if n == 500 { &small } else { &large };
        let _ = std::hint::black_box(decide(f));
    });
}

#[test]
fn decide_scales_over_a_chain_with_a_disjunction_every_fourth_stage() {
    let (small, large) = (
        chain_with_disjunctions(400, 4),
        chain_with_disjunctions(400 * scaling::FACTOR, 4),
    );
    assert_eq!((decide(&small), decide(&large)), (Ok(true), Ok(true)));
    for f in [&small, &large] {
        let m = satisfiable(f).unwrap().expect("a point");
        assert!(f.holds(&m), "{m:?}");
    }
    scaling::check_order(
        "decide on a chain with a disjunction every fourth stage",
        400,
        1,
        |n| {
            let f = if n == 400 { &small } else { &large };
            let _ = std::hint::black_box(decide(f));
        },
    );
}

#[test]
fn decide_on_tied_disjunctions_scales() {
    let (small, large) = (
        star_with_choices(4400),
        star_with_choices(4400 * scaling::FACTOR),
    );
    assert_eq!((decide(&small), decide(&large)), (Ok(true), Ok(true)));
    scaling::check_order(
        "decide on a star of tied leaves with choices",
        4400,
        1,
        |n| {
            let f = if n == 4400 { &small } else { &large };
            let _ = std::hint::black_box(decide(f));
        },
    );
}

#[test]
fn satisfiable_on_tied_disjunctions_scales() {
    let (small, large) = (
        star_with_choices(4900),
        star_with_choices(4900 * scaling::FACTOR),
    );
    for f in [&small, &large] {
        let m = satisfiable(f).unwrap().expect("a point");
        assert!(f.holds(&m), "{m:?}");
    }
    scaling::check_order(
        "a point of a star of tied leaves with choices",
        4900,
        1,
        |n| {
            let f = if n == 4900 { &small } else { &large };
            let _ = std::hint::black_box(satisfiable(f));
        },
    );
}

#[test]
fn project_each_on_tied_disjunctions_scales() {
    // A leaf and a hub of the star: no disjunct is shown to have no point, and the hulls are
    // those of the star alone (a leaf in `[0, 23]`, `h1` in `[0, 5]`), each disjunction kept.
    let (small, large) = (
        star_with_choices(770),
        star_with_choices(770 * scaling::FACTOR),
    );
    let v = |i: usize| Atom::Sym(format!("v{i}").into());
    let syms = [v(2), v(0)];
    for f in [&small, &large] {
        let (each, skipped) = project_each(f, &syms).unwrap();
        let hulls: Vec<String> = each
            .iter()
            .map(|s| s.as_ref().unwrap().to_string())
            .collect();
        assert_eq!(hulls, ["[0..=23]", "[0..=5]"]);
        assert_eq!(skipped, Vec::new());
    }
    scaling::check_order(
        "projections of a star of tied leaves with choices",
        770,
        1,
        |n| {
            let f = if n == 770 { &small } else { &large };
            let _ = std::hint::black_box(project_each(f, &syms));
        },
    );
}

#[test]
fn decide_on_separate_tied_disjunctions_scales() {
    // Settling tests each disjunct against its own pair, and `alone` reads each row once.
    let (small, large) = (separate_pairs(9000), separate_pairs(9000 * scaling::FACTOR));
    assert_eq!((decide(&small), decide(&large)), (Ok(true), Ok(true)));
    let m = satisfiable(&large).unwrap().expect("a point");
    assert!(large.holds(&m), "{m:?}");
    scaling::check_order("decide on separate pairs of tied atoms", 9000, 1, |n| {
        let f = if n == 9000 { &small } else { &large };
        let _ = std::hint::black_box(decide(f));
    });
}
