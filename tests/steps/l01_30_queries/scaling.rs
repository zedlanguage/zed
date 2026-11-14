//! Queries at the rule of low complexity (DESIGN.md Part G). Asking again after an edit to one
//! definition of `n` reruns the front end and one row; finding each kept result by a search of
//! those kept, or keying each row by every definition of the unit, would take `O(n²)`. The
//! benchmarks in `bench/scaling.rs` hold both linear; here each runs at small sizes.

use zedc::query::{Db, Key, Query, key};

use super::checks;

/// `n` functions `g0`, `g1`, …, each with one row, the first scaled by `k` (`f64` would name a
/// type).
pub(super) fn tables(n: usize, k: usize) -> String {
    (0..n)
        .map(|i| {
            let (scale, want) = if i == 0 { (k, k) } else { (1, i + 1) };
            format!("g{i}(positional x) = x * {scale} + {i} test {{ 1 -> {want} }}\n")
        })
        .collect()
}

/// A database that has checked `tables(n, 1)`, and the scale 1.
pub(super) fn checked(n: usize) -> (Db, usize) {
    let mut db = Db::new();
    checks(&mut db, &tables(n, 1));
    (db, 1)
}

/// Edits the scale of the first of `n` functions checked in `db`: every row passes, and the
/// one row the edit reaches is the one checked again.
pub(super) fn rechecks_one_row(db: &mut Db, k: &mut usize, n: usize) {
    *k += 1;
    let text = tables(n, *k);
    let before = db.computed(Query::Row);
    let got = checks(db, &text);
    assert_eq!(got.len(), n);
    assert!(got.iter().all(|o| o.ends_with(": ok")), "{}", got[0]);
    assert_eq!(db.computed(Query::Row), before + 1);
}

/// The keys of `n` rows.
pub(super) fn row_keys(n: usize) -> Vec<Key> {
    (0..n)
        .map(|i| key("row", &[i.to_string().as_bytes()]))
        .collect()
}

/// Keeps a result for each of `keys` and asks for each again: each answer is the one kept, and
/// each row is computed once.
pub(super) fn keeps_and_finds_each(keys: &[Key]) {
    let mut db = Db::new();
    // A row's result is `Ok(())` or its failure; the failure `i` tells the rows apart.
    for (i, k) in keys.iter().enumerate() {
        let _ = db.row(Query::Row, k.clone(), || Err(i.to_string()));
    }
    for (i, k) in keys.iter().enumerate() {
        let again = db.row(Query::Row, k.clone(), || Err("again".into()));
        assert_eq!(again, Err(i.to_string()));
    }
    assert_eq!(db.computed(Query::Row), keys.len());
}

#[test]
fn asking_again_after_an_edit_to_one_of_a_few_definitions_checks_one_row() {
    for n in [1, 2, 9] {
        let (mut db, mut k) = checked(n);
        for _ in 0..3 {
            rechecks_one_row(&mut db, &mut k, n);
        }
    }
}

#[test]
fn a_few_kept_results_are_each_found_again() {
    for n in [0, 1, 2, 9] {
        keeps_and_finds_each(&row_keys(n));
    }
}
