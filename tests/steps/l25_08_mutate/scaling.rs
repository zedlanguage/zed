//! The rule of low complexity (DESIGN.md Part G): finding the mutants reads each node once,
//! and a mutant costs its definition and the rows that reach it, not the unit.

use std::cell::RefCell;
use std::collections::BTreeMap;

use zed_tests::deep::on_main_sized_stack;
use zed_tests::scaling;
use zedc::mutate;
use zedc::query::Db;
use zedc::run;

/// A table of fixed size beside `n` functions no row reaches, each with one operator and one
/// constant: `3n + 3` mutants.
fn unit(n: usize) -> String {
    let mut text =
        String::from("isChild(positional age) = age <= 12 test { 12 -> true, 13 -> false }\n");
    for i in 0..n {
        text += &format!("g{i}(positional x) = x + {i};\n");
    }
    text
}

/// One definition with `n` additions in a chain: `x + 1 + 1 + …`, `2n` operator and constant
/// nodes, nested `n` deep.
fn chain(n: usize) -> String {
    format!("f(positional x) = x{};\n", " + 1".repeat(n))
}

/// The front end's result for each size, made once, so that only the mutants are timed.
type Warm = RefCell<BTreeMap<usize, (String, Db)>>;

fn warm(warm: &Warm, n: usize, make: fn(usize) -> String) -> (String, Db) {
    let mut warm = warm.borrow_mut();
    let (text, db) = warm.entry(n).or_insert_with(|| {
        let text = make(n);
        let mut db = Db::new();
        db.front(&text);
        (text, db)
    });
    (text.clone(), db.clone())
}

#[test]
fn finding_the_mutants_scales() {
    // The front end elaborates a chain by recursion, as deep as the chain: a main thread's stack.
    on_main_sized_stack(finding);
}

fn finding() {
    for (what, make, per) in [
        (
            "finding the mutants of n functions",
            unit as fn(usize) -> String,
            3,
        ),
        ("finding the mutants of a chain of n additions", chain, 3),
    ] {
        let cache = Warm::default();
        scaling::check_order(what, 100, 1, |n| {
            let (text, mut db) = warm(&cache, n, make);
            let front = db.front(&text);
            let (stmts, unit) = front.as_ref().as_ref().unwrap();
            let found = mutate::mutants(&text, stmts, unit).unwrap();
            assert!(found.len() >= per * n, "{}", found.len());
        });
    }
}

#[test]
fn running_the_mutants_against_a_fixed_table_scales() {
    let cache = Warm::default();
    scaling::check_order(
        "running the mutants of n functions and a fixed table",
        100,
        1,
        |n| {
            let (text, mut db) = warm(&cache, n, unit);
            let front = db.front(&text);
            let (stmts, unit) = front.as_ref().as_ref().unwrap();
            let found = mutate::run(&text, stmts, unit, &run::direct).unwrap();
            assert_eq!(found.len(), 3 * n + 3);
        },
    );
}
