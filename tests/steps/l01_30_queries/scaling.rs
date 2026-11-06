//! Queries at the rule of low complexity (DESIGN.md Part G). Asking again after an edit to one
//! definition of `n` reruns the front end and one row; finding each kept result by a search of
//! those kept, or keying each row by every definition of the unit, would take `O(n²)`.

use std::collections::HashMap;
use std::sync::Mutex;

use zed_tests::scaling::{FACTOR, check, inputs};
use zedc::query::{Db, Query, key};

use super::checks;

/// `n` functions `g0`, `g1`, …, each with one row, the first scaled by `k` (`f64` would name a
/// type).
fn tables(n: usize, k: usize) -> String {
    (0..n)
        .map(|i| {
            let (scale, want) = if i == 0 { (k, k) } else { (1, i + 1) };
            format!("g{i}(positional x) = x * {scale} + {i} test {{ 1 -> {want} }}\n")
        })
        .collect()
}

#[test]
fn asking_again_after_an_edit_to_one_of_many_definitions_scales() {
    // Each size keeps its database and the scale of its first function, and each run edits
    // that scale, so a run rechecks the one row the edit reaches.
    let dbs: HashMap<usize, Mutex<(Db, usize)>> = [200, FACTOR * 200]
        .into_iter()
        .map(|n| {
            let mut db = Db::new();
            checks(&mut db, &tables(n, 1));
            (n, Mutex::new((db, 1)))
        })
        .collect();
    check(
        "checking n functions' rows again after one edit",
        200,
        |n| {
            let mut held = dbs[&n].lock().unwrap();
            let (db, k) = &mut *held;
            *k += 1;
            let text = tables(n, *k);
            let before = db.computed(Query::Row);
            let got = checks(db, &text);
            assert_eq!(got.len(), n);
            assert!(got.iter().all(|o| o.ends_with(": ok")), "{}", got[0]);
            assert_eq!(db.computed(Query::Row), before + 1);
        },
    );
}

#[test]
fn keeping_many_results_and_asking_for_each_again_scales() {
    let keys = inputs(5_000, |n| {
        (0..n)
            .map(|i| key("row", &[i.to_string().as_bytes()]))
            .collect::<Vec<_>>()
    });
    check("keeping n results and asking for each again", 5_000, |n| {
        let mut db = Db::new();
        // A row's result is `Ok(())` or its failure; the failure `i` tells the rows apart.
        for (i, k) in keys[&n].iter().enumerate() {
            let _ = db.row(Query::Row, k.clone(), || Err(i.to_string()));
        }
        for (i, k) in keys[&n].iter().enumerate() {
            let again = db.row(Query::Row, k.clone(), || Err("again".into()));
            assert_eq!(again, Err(i.to_string()));
        }
        assert_eq!(db.computed(Query::Row), n);
    });
}
