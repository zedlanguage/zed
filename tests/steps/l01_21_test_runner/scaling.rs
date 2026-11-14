//! The runner at the rule of low complexity (DESIGN.md Part G). Each row was keyed by a scan
//! of every definition of the unit and run under all of them as lets, so a unit of `n`
//! functions with a row each took `O(n²)`; a row now reads only the definitions it reaches. The
//! benchmarks of `bench.rs` hold that order; here each of their checks is made at small sizes.

use zedc::query::Db;
use zedc::testing::test_in;

use zed_tests::step_helpers::l01_16_elaboration::{Checked, checked};

/// `n` functions, each with one row, beside a constant each that no row reads.
pub(super) fn tables(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!(
                "c{i} = {i} * 2;\nh{i}(positional x) = x + {i} test {{ 1 -> {} }}\n",
                i + 1
            )
        })
        .collect()
}

/// `n` functions with a declared parameter, each with a row whose key is an atom the parameter
/// does not take, so each row's call passes it by (rule 6), beside one whose key the body takes.
pub(super) fn passing_rows(n: usize) -> String {
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
pub(super) fn wide_row(n: usize) -> String {
    let params: Vec<String> = (0..n).map(|i| format!("positional p{i}: int")).collect();
    let key: Vec<String> = (0..n).map(|i| format!("#a{i}")).collect();
    format!(
        "first({}) = p0\ntest {{ ({}) -> #a0 }}\n",
        params.join(", "),
        key.join(", ")
    )
}

/// `n` functions with a row each, in a unit a marked line rejects, so no row runs.
pub(super) fn rejected_rows(n: usize) -> String {
    let mut text = tables(n);
    text.push_str("c0 = 1;    // ✗ Rebinding in the same scope: c0 is bound above\n");
    text
}

/// `main` with `n` tables, each with a clause giving `main::files` and `rows` rows, every row
/// reading the file its clause gives.
pub(super) fn clause_tables(n: usize, rows: usize) -> String {
    let mut text =
        String::from("main(m: MainArgs) {\n  m.stdout <- main::files[\"a\"] else \"\";\n}\n");
    for i in 0..n {
        let row = format!("\"\" -> \"{i}\\n\"");
        let rows = vec![row; rows].join(", ");
        text.push_str(&format!(
            "test with main::files = (p -> \"{i}\") {{ {rows} }}\n"
        ));
    }
    text
}

/// `text` with the front end's result held, so that a run of its rows on a copy of the `Db`
/// times the rows alone.
pub(super) fn warm(text: String) -> (String, Db) {
    let mut db = Db::new();
    db.front(&text);
    (text, db)
}

/// The rows of `text`, run on a copy of `db`, are `rows` in number and all pass.
pub(super) fn all_rows_pass((text, db): &(String, Db), rows: usize) {
    let got = test_in(&mut db.clone(), text);
    assert_eq!(got.len(), rows);
    assert!(
        got.iter().all(|o| o.failure.is_none()),
        "{:?}",
        got.iter().find_map(|o| o.failure.as_ref())
    );
}

/// The `n` rows of the rejected unit `rejected_rows(n)` are each reported as not run, beside
/// the marked line's check.
pub(super) fn rows_not_run((text, db): &(String, Db), n: usize) {
    let got = test_in(&mut db.clone(), text);
    assert_eq!(got.len(), n + 1);
    let not_run = got
        .iter()
        .filter(|o| {
            o.failure
                .as_deref()
                .is_some_and(|w| w.ends_with("not run, since the unit is rejected"))
        })
        .count();
    assert_eq!(not_run, n);
}

/// The checked unit elaborates to `tests` rows.
pub(super) fn elaborates_rows(unit: &Checked, tests: usize) {
    assert_eq!(unit.elab().tests.len(), tests);
}

#[test]
fn the_rows_of_each_benchmark_unit_run_at_small_sizes() {
    for n in [1, 2, 9] {
        all_rows_pass(&warm(tables(n)), n);
        all_rows_pass(&warm(passing_rows(n)), 2 * n);
        rows_not_run(&warm(rejected_rows(n)), n);
        elaborates_rows(&checked(&wide_row(n)), 1);
        elaborates_rows(&checked(&clause_tables(n, 1)), n);
        all_rows_pass(&warm(clause_tables(1, n)), n);
    }
}

#[test]
fn a_row_passing_the_atoms_of_many_arguments_fails_with_their_merge() {
    // The atoms of every argument merge, as at a call.
    let got = test_in(&mut Db::new(), &wide_row(8));
    assert_eq!(got.len(), 1);
    let why = got[0].failure.as_deref().unwrap_or("");
    assert!(why.contains("the result is #errs("), "{why}");
}
