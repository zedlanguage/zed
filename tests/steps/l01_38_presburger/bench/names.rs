//! The benchmarks of `names.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::names::*;
use zed_tests::scaling;
use zedc::store::presburger::{decide, project_each, satisfiable};

#[test]
fn decide_scales_over_copies_of_a_tie() {
    // Each copy of the five-variable counterexample is refused with a tie.
    scales_over_copies("copies of a tie", &claude5(), 5, 72);
}

#[test]
fn decide_scales_over_copies_of_a_system_with_tied_variables() {
    // Each copy of Codex's six-variable system, whose variables tie, has a point.
    scales_over_copies("copies of Codex's system", &codex6(), 6, 40);
}

#[test]
fn decide_scales_over_copies_of_tied_equalities() {
    // Each copy of `x + y == 5`, `x, y >= 0` keeps its equality as rows and has a point.
    scales_over_copies("copies of tied equalities", &tied_equalities(), 2, 180);
}

#[test]
fn decide_scales_over_one_class_of_equalities() {
    // `Ties` joins every equality of the class, and `representatives` reads each variable's
    // root once; with union by rank both cost a logarithm per variable.
    let (small, large) = (
        one_class_of_equalities(38000),
        one_class_of_equalities(38000 * scaling::FACTOR),
    );
    assert_eq!((decide(&small), decide(&large)), (Ok(true), Ok(true)));
    scaling::check_order("decide on one class of equalities", 38000, 1, |n| {
        let f = if n == 38000 { &small } else { &large };
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
    let syms = leaf_and_hub();
    for f in [&small, &large] {
        assert_star_hulls(f, &syms);
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

/// `names::tied_equalities_that_share_only_a_variable_they_do_not_define_are_solved_together`
/// as first written, 1.19 s (2026-11-14, load 25): every one of the 5040 namings of each system.
#[test]
fn tied_equalities_that_share_only_a_variable_they_do_not_define_are_solved_together_in_any_naming()
{
    for (rows, want) in tied_remainder_systems() {
        assert_eq!(namings(&rows, 7).into_keys().collect::<Vec<_>>(), [want]);
    }
}

/// `names::the_splinters_are_searched_a_batch_at_a_time` as first written, 0.68 s (2026-11-14,
/// load 14), at a fixed seed: 60 namings of the chain of six and 20 of the chain of twelve.
#[test]
fn the_splinters_are_searched_a_batch_at_a_time_under_80_namings_of_seed_0x5b1() {
    splinters_answer_alike(&mut zed_tests::instances::Rng::new(0x5b1), 60, 20, 0x5b1);
}
