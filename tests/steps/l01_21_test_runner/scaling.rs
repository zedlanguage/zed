//! The runner at the rule of low complexity (DESIGN.md Part G). Each row was keyed by a scan
//! of every definition of the unit and run under all of them as lets, so a unit of `n`
//! functions with a row each took `O(n²)`; a row now reads only the definitions it reaches.

use std::cell::RefCell;
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
    // The front end's result for each size, made once, so that the rows alone are timed.
    let warm: RefCell<BTreeMap<usize, (String, Db)>> = RefCell::default();
    scaling::check("running n functions' rows", 100, |n| {
        let (text, mut db) = {
            let mut warm = warm.borrow_mut();
            let (text, db) = warm.entry(n).or_insert_with(|| {
                let text = tables(n);
                let mut db = Db::new();
                db.front(&text);
                (text, db)
            });
            (text.clone(), db.clone())
        };
        let got = test_in(&mut db, &text);
        assert_eq!(got.len(), n);
        assert!(
            got.iter().all(|o| o.failure.is_none()),
            "{:?}",
            got[0].failure
        );
    });
}
