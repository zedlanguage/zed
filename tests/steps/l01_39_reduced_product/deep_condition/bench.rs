//! Benchmarks of `deep_condition`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

/// Runs `f` on a thread whose stack holds the recursion over a term nested 2000 deep.
fn on_a_deep_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(f)
        .expect("a thread")
        .join()
        .expect("the test passes");
}

#[test]
fn arms_of_a_deep_test_take_time_near_linear_in_its_depth() {
    // The tests are built before the measurement, so that only `arms` is measured.
    let tests: BTreeMap<usize, Term> = [60, 480].map(|d| (d, fallbacks(d))).into();
    let scope = ints(&["x".into(), "y".into()]);
    scaling::check("arms of a test nested d deep", 60, |d| {
        let t = if_(tests[&d].clone(), lit(1), lit(2));
        std::hint::black_box(arms(&t, &scope));
    });
}

#[test]
fn arms_of_a_deeper_test_take_time_near_linear_in_its_depth() {
    // Depths 600 and 4800, where a cost quadratic in the depth is plain.
    on_a_deep_stack(|| {
        let tests: BTreeMap<usize, Term> = [600, 4800]
            .map(|d| (d, if_(fallbacks(d), lit(1), lit(2))))
            .into();
        let scope = ints(&["x".into(), "y".into()]);
        scaling::check("arms of a test nested d deep", 600, |d| {
            std::hint::black_box(arms(&tests[&d], &scope));
        });
    });
}

#[test]
fn arms_of_a_test_with_two_choices_per_level_take_time_near_linear_in_its_depth() {
    on_a_deep_stack(|| {
        let tests: BTreeMap<usize, Term> = [400, 3200]
            .map(|d| (d, if_(two_choices(d), lit(1), lit(2))))
            .into();
        let scope = ints(&["x".into(), "y".into(), "z".into()]);
        for n in [400] {
            scaling::check("arms of a test with two choices per level", n, |d| {
                std::hint::black_box(arms(&tests[&d], &scope));
            });
        }
    });
}

#[test]
fn relations_of_a_deep_test_take_time_near_linear_in_its_depth() {
    // The translation of the test into the linear-relation domain, alone: each level is
    // translated once, not once for each level above it.
    on_a_deep_stack(|| {
        let tests: BTreeMap<usize, Term> = [6000, 48000].map(|d| (d, fallbacks(d))).into();
        let names: [Arc<str>; 2] = ["x".into(), "y".into()];
        scaling::check("relations of a test nested d deep", 6000, |d| {
            std::hint::black_box(relations(&[&tests[&d]], &names, false));
        });
    });
}

#[test]
fn arms_of_a_chain_of_accounts_take_time_near_linear_in_its_depth() {
    // Each level names two new symbols, so a level that asked for every symbol below it would
    // cost the depth once for each level.
    on_a_deep_stack(|| {
        let cases: BTreeMap<usize, (Term, Scope)> = [60, 480]
            .map(|d| {
                (
                    d,
                    (if_(accounts(d), lit(1), lit(2)), ints(&account_names(d))),
                )
            })
            .into();
        scaling::check("arms of a chain of accounts d deep", 60, |d| {
            let (t, scope) = &cases[&d];
            std::hint::black_box(arms(t, scope));
        });
    });
}

#[test]
fn arms_of_a_long_chain_of_accounts_take_time_within_n_log_n() {
    // A lookup of a conjunct in the relation's maps finds the very formula it holds; compared
    // in full, the nest below the level, each lookup cost the depth: 0.85 and 13.19 G
    // instructions at d = 240 and 1920, 15.5 times. Now 0.76 and 7.84 G, 10.2 times.
    on_a_deep_stack(|| {
        let cases: BTreeMap<usize, (Term, Scope)> = [240, 1920]
            .map(|d| {
                (
                    d,
                    (if_(accounts(d), lit(1), lit(2)), ints(&account_names(d))),
                )
            })
            .into();
        scaling::check("arms of a chain of accounts d deep", 240, |d| {
            let (t, scope) = &cases[&d];
            std::hint::black_box(arms(t, scope));
        });
    });
}

#[test]
fn arms_of_a_chain_of_paired_choices_take_time_within_n_log_n() {
    // Most cases of a level fail. Each failed case emptied every name in scope, the depth
    // of them: 1.45 and 22.16 G instructions at d = 120 and 960, 15.2 times. A failed case
    // is dropped, so now only a scope that is shown is emptied: 1.31 and 11.56 G, 8.8 times.
    on_a_deep_stack(|| {
        let cases: BTreeMap<usize, (Term, Scope)> = [120, 960]
            .map(|d| {
                (
                    d,
                    (if_(paired_chain(d), lit(1), lit(2)), ints(&paired_names(d))),
                )
            })
            .into();
        scaling::check("arms of a chain of paired choices d deep", 120, |d| {
            let (t, scope) = &cases[&d];
            std::hint::black_box(arms(t, scope));
        });
    });
}

#[test]
fn arms_of_a_capped_test_take_time_near_linear_in_its_depth() {
    // Two disjunctions and a hull with two finite bounds at each level, the case a level
    // tightens; a tightening over the whole nest below each level would cost its depth.
    on_a_deep_stack(|| {
        let tests: BTreeMap<usize, Term> = [300, 2400]
            .map(|d| (d, if_(capped(d), lit(1), lit(2))))
            .into();
        let scope = ints(&["x".into(), "y".into(), "z".into()]);
        scaling::check("arms of a capped test nested d deep", 300, |d| {
            std::hint::black_box(arms(&tests[&d], &scope));
        });
    });
}

#[test]
fn arms_of_a_test_whose_bound_moves_at_each_level_take_time_near_linear_in_its_depth() {
    // Each level tightens the hull of `x`; a tightening over the whole nest below each level,
    // or a search that reads again the nest below each level, would cost its depth.
    on_a_deep_stack(|| {
        let tests: BTreeMap<usize, Term> = [120, 960]
            .map(|d| (d, if_(moving(d), lit(1), lit(2))))
            .into();
        let scope = ints(&level_names());
        scaling::check("arms of a test whose bound moves at each level", 120, |d| {
            std::hint::black_box(arms(&tests[&d], &scope));
        });
    });
}

#[test]
fn arms_of_a_test_whose_small_choice_misses_the_bound_take_time_near_linear_in_its_depth() {
    // A point at the bound is found only below every level, so a search that read the nest
    // below each level again would cost its depth.
    on_a_deep_stack(|| {
        let tests: BTreeMap<usize, Term> = [180, 1440]
            .map(|d| (d, if_(heavy(d), lit(1), lit(2))))
            .into();
        let scope = ints(&level_names());
        scaling::check(
            "arms of a test whose small choice misses the bound",
            180,
            |d| {
                std::hint::black_box(arms(&tests[&d], &scope));
            },
        );
    });
}

#[test]
fn the_search_for_a_point_tests_each_part_of_a_deeper_test_a_bounded_number_of_times() {
    // A count, not a time: at depths 60 and 480 a search without `Parts::failed` tests 516 and
    // 3876 parts per level of `heavy`, far above the bound of 48 (see
    // `the_search_for_a_point_tests_each_part_of_a_deep_test_a_bounded_number_of_times`).
    on_a_deep_stack(|| parts_tested_per_level([60, 480]));
}
