//! Asking again after an edit to one of many definitions, and finding each of many kept
//! results, are linear: the benchmarks of `scaling.rs`, whose tests run each at small sizes.

use std::collections::HashMap;
use std::sync::Mutex;

use zed_tests::scaling::{FACTOR, check, inputs};
use zedc::query::Db;

use crate::scaling::{checked, keeps_and_finds_each, rechecks_one_row, row_keys};

#[test]
fn asking_again_after_an_edit_to_one_of_many_definitions_scales() {
    // Each size keeps its database and the scale of its first function, and each run edits
    // that scale, so a run rechecks the one row the edit reaches.
    let dbs: HashMap<usize, Mutex<(Db, usize)>> = [200, FACTOR * 200]
        .into_iter()
        .map(|n| (n, Mutex::new(checked(n))))
        .collect();
    check(
        "checking n functions' rows again after one edit",
        200,
        |n| {
            let mut held = dbs[&n].lock().unwrap();
            let (db, k) = &mut *held;
            rechecks_one_row(db, k, n);
        },
    );
}

#[test]
fn keeping_many_results_and_asking_for_each_again_scales() {
    let keys = inputs(5_000, row_keys);
    check("keeping n results and asking for each again", 5_000, |n| {
        keeps_and_finds_each(&keys[&n]);
    });
}
