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
                "c{i} = {i} * 2;\nf{i}(positional x) = x + {i} test {{ 1 -> {} }}\n",
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
