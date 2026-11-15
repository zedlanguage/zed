//! The benchmarks of `names.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::names::*;
use zed_tests::scaling;
use zedc::store::presburger::{Atom, Con, Formula, Lin, decide, project_each, satisfiable};

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

/// The size of `decide_scales_over_copies_of_the_or_if_question`.
const K: usize = 2000;

/// `k` copies of the question of plan row FAIL-or-if-tie-refusal: `x` in `-6..=-1` or `1..=6`,
/// `y` as `x` (`y_may_be_zero` false, no point) or in `-6..=6` (true), and `x == 0 || y == 0`.
/// Atoms of different copies share a color, and the first swap in name order is no symmetry (it
/// moves one copy's `x` into another's), so `Numbered::ties_are_symmetries` ends at it; the
/// copies share no atom and are decided one by one.
fn copies_of_the_or_if_question(k: usize, y_may_be_zero: bool) -> Formula {
    let v = |name: String| Lin::atom(Atom::Sym(name.into()));
    let c = |x: i64| Lin::constant(x);
    let within_six = |a: &Lin| {
        vec![
            Formula::Con(Con::ge(a, &c(-6))),
            Formula::Con(Con::ge(&c(6), a)),
        ]
    };
    let away_from_zero = |a: &Lin| {
        let mut fs = within_six(a);
        fs.push(Formula::or(vec![
            Formula::Con(Con::ge(&c(-1), a)),
            Formula::Con(Con::ge(a, &c(1))),
        ]));
        Formula::and(fs)
    };
    let mut fs = Vec::new();
    for i in 0..k {
        let (x, y) = (v(format!("x{i}")), v(format!("y{i}")));
        fs.push(away_from_zero(&x));
        fs.push(match y_may_be_zero {
            false => away_from_zero(&y),
            true => Formula::and(within_six(&y)),
        });
        fs.push(Formula::or(vec![
            Formula::Con(Con::eq(&x, &c(0))),
            Formula::Con(Con::eq(&y, &c(0))),
        ]));
    }
    Formula::and(fs)
}

#[test]
fn decide_scales_over_copies_of_the_or_if_question() {
    // Satisfied and projected as decided: one copy and two alike.
    for k in [1, 2] {
        let f = copies_of_the_or_if_question(k, false);
        assert_eq!(
            (decide(&f), satisfiable(&f)),
            (Ok(false), Ok(None)),
            "{k} copies"
        );
        let (each, skipped) = project_each(&f, &[Atom::Sym("x0".into())]).unwrap();
        assert!(skipped.is_empty() && each[0].as_ref().unwrap().pieces().next().is_none());
        // With `y` free to be 0 there is a point, and the one found is one: each `y` is 0.
        let f = copies_of_the_or_if_question(k, true);
        assert_eq!(decide(&f), Ok(true), "{k} copies");
        let m = satisfiable(&f).unwrap().expect("a point");
        for i in 0..k {
            let at = |s: String| m[&Atom::Sym(s.into())].clone();
            let (x, y) = (at(format!("x{i}")), at(format!("y{i}")));
            assert!(y == 0.into() && x != 0.into(), "copy {i}: x = {x}, y = {y}");
        }
    }
    let (small, large) = (
        copies_of_the_or_if_question(K, false),
        copies_of_the_or_if_question(K * scaling::FACTOR, false),
    );
    assert_eq!((decide(&small), decide(&large)), (Ok(false), Ok(false)));
    scaling::check_order("decide on copies of the or-if question", K, 1, |n| {
        let f = if n == K { &small } else { &large };
        let _ = std::hint::black_box(decide(f));
    });
}
