//! The runner at the rule of low complexity (DESIGN.md Part G). Each row was keyed by a scan
//! of every definition of the unit and run under all of them as lets, so a unit of `n`
//! functions with a row each took `O(n²)`; a row now reads only the definitions it reaches.

use std::collections::BTreeMap;

use zed_tests::scaling;
use zedc::query::Db;
use zedc::testing::test_in;

/// `n` functions, each with one row, beside a constant each that no row reads.
fn tables(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!(
                "c{i} = {i} * 2;\nh{i}(positional x) = x + {i} test {{ 1 -> {} }}\n",
                i + 1
            )
        })
        .collect()
}

#[test]
fn running_the_rows_of_many_tables_scales() {
    // The front end's result for each size, made before the timing, so that the rows alone are
    // timed. Each run runs them on a copy, which holds the front end's results and no row's.
    let n = 100;
    let warm: BTreeMap<usize, (String, Db)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let text = tables(m);
            let mut db = Db::new();
            db.front(&text);
            (m, (text, db))
        })
        .collect();
    scaling::check("running n functions' rows", n, |m| {
        let (text, db) = &warm[&m];
        let got = test_in(&mut db.clone(), text);
        assert_eq!(got.len(), m);
        assert!(
            got.iter().all(|o| o.failure.is_none()),
            "{:?}",
            got[0].failure
        );
    });
}

/// `n` functions with a declared parameter, each with a row whose key is an atom the parameter
/// does not take, so each row's call passes it by (rule 6), beside one whose key the body takes.
fn passing_rows(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!(
                "h{i}(positional x: int) = x + {i} test {{ #gone{i} -> #gone{i}, 1 -> {} }}\n",
                i + 1
            )
        })
        .collect()
}

/// One function of `n` parameters with a row whose key gives each an atom it does not take.
fn wide_row(n: usize) -> String {
    let params: Vec<String> = (0..n).map(|i| format!("positional p{i}: int")).collect();
    let key: Vec<String> = (0..n).map(|i| format!("#a{i}")).collect();
    format!(
        "first({}) = p0\ntest {{ ({}) -> #a0 }}\n",
        params.join(", "),
        key.join(", ")
    )
}

/// `n` functions with a row each, in a unit a marked line rejects, so no row runs.
fn rejected_rows(n: usize) -> String {
    let mut text = tables(n);
    text.push_str("bad = 1 + \"s\";    // ✗\n");
    text
}

/// The checks of each size of `unit`, made before the timing with the front end's result held,
/// so that a run times the rows: each run runs them on a copy of that `Db`.
fn warm(n: usize, unit: fn(usize) -> String) -> BTreeMap<usize, (String, Db)> {
    [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let text = unit(m);
            let mut db = Db::new();
            db.front(&text);
            (m, (text, db))
        })
        .collect()
}

#[test]
fn rows_whose_calls_pass_atoms_by_scale() {
    let n = 100;
    let warm = warm(n, passing_rows);
    scaling::check("running n rows whose keys pass atoms", n, |m| {
        let (text, db) = &warm[&m];
        let got = test_in(&mut db.clone(), text);
        assert_eq!(got.len(), 2 * m);
        assert!(
            got.iter().all(|o| o.failure.is_none()),
            "{:?}",
            got.iter().find_map(|o| o.failure.as_ref())
        );
    });
}

#[test]
fn a_row_passing_the_atoms_of_many_arguments_scales() {
    let n = 100;
    let warm = warm(n, wide_row);
    scaling::check("a row of n arguments that each pass an atom", n, |m| {
        let (text, db) = &warm[&m];
        let got = test_in(&mut db.clone(), text);
        assert_eq!(got.len(), 1);
        // The atoms of every argument merge, as at a call.
        let why = got[0].failure.as_deref().unwrap_or("");
        assert!(why.contains("the result is #errs("), "{why}");
    });
}

#[test]
fn the_rows_of_a_rejected_unit_fail_in_linear_time() {
    let n = 400;
    let warm = warm(n, rejected_rows);
    scaling::check("reporting the n rows of a rejected unit", n, |m| {
        let (text, db) = &warm[&m];
        let got = test_in(&mut db.clone(), text);
        assert_eq!(got.len(), m + 1);
        let not_run = got
            .iter()
            .filter(|o| {
                o.failure
                    .as_deref()
                    .is_some_and(|w| w.ends_with("not run, since the unit is rejected"))
            })
            .count();
        assert_eq!(not_run, m);
    });
}
