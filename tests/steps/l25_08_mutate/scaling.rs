//! The rule of low complexity (DESIGN.md Part G): finding the mutants reads each node once,
//! and a mutant costs its definition and the rows that reach it, not the unit.

use std::collections::BTreeMap;
use std::sync::Mutex;

use zed_tests::deep::on_main_sized_stack;
use zed_tests::scaling;
use zedc::mutate::{self, Verdict};
use zedc::query::Db;
use zedc::run;

/// `n` functions, each with one operator, one constant and a row of its own, beside a table
/// of fixed size: `3n + 3` mutants, each of which runs the one row that reaches its
/// definition, so the run measures what a mutant's rows cost.
fn unit(n: usize) -> String {
    let mut text =
        String::from("isChild(positional age) = age <= 12 test { 12 -> true, 13 -> false }\n");
    for i in 0..n {
        text += &format!("g{i}(positional x) = x + {i} test {{ 0 -> {i} }}\n");
    }
    text
}

/// One definition with `n` additions in a chain: `x + 1 + 1 + …`, `2n` operator and constant
/// nodes, nested `n` deep.
fn chain(n: usize) -> String {
    format!("f(positional x) = x{};\n", " + 1".repeat(n))
}

/// The front end's result for each size, made once, so that only the mutants are timed.
type Warm = Mutex<BTreeMap<usize, (String, Db)>>;

fn warm(warm: &Warm, n: usize, make: fn(usize) -> String) -> (String, Db) {
    let mut warm = warm.lock().unwrap();
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
            let (stmts, unit, _) = front.as_ref().as_ref().unwrap();
            let found = mutate::mutants(&text, stmts, unit).unwrap();
            assert!(found.len() >= per * n, "{}", found.len());
        });
    }
}

#[test]
fn running_the_mutants_of_n_functions_each_with_a_row_scales() {
    let cache = Warm::default();
    scaling::check_order(
        "running the mutants of n functions, each with a row",
        100,
        1,
        |n| {
            let (text, mut db) = warm(&cache, n, unit);
            let front = db.front(&text);
            let (stmts, unit, _) = front.as_ref().as_ref().unwrap();
            let found = mutate::run(&text, stmts, unit, &run::direct).unwrap();
            assert_eq!(found.len(), 3 * n + 3);
            // Each mutant ran its row; only `x + 0` replaced by `x - 0` in `g0` passes it.
            let detected = found
                .iter()
                .filter(|(_, v)| *v == Verdict::Detected)
                .count();
            assert_eq!(detected, 3 * n + 2);
        },
    );
}

/// One definition with `n` additions in a chain and a row that checks its sum: `3n` mutants
/// (each `+` by `-`, each `1` by `0` and by `2`), each of which copies, remixes and runs the
/// whole definition, so the run is of order n². `x` is declared `int`, so each `1` is an `int`.
fn chain_with_row(n: usize) -> String {
    format!(
        "f(positional x: int) = x{} test {{ 0 -> {n} }}\n",
        " + 1".repeat(n)
    )
}

/// [`chain_with_row`] with `x` undeclared: each `1` takes the carrier of `x` (DESIGN.md L1.26a),
/// one `match` on it per literal, and each mutant runs about 6 times the work of the `int`
/// chain's (COMPLEXITY.md F135).
fn generic_chain_with_row(n: usize) -> String {
    format!(
        "f(positional x) = x{} test {{ 0 -> {n} }}\n",
        " + 1".repeat(n)
    )
}

#[test]
fn running_the_mutants_of_a_chain_of_n_additions_scales() {
    // The front end elaborates a chain by recursion, as deep as the chain: a main thread's stack.
    on_main_sized_stack(|| running_a_chain("", 100, chain_with_row));
}

#[test]
fn running_the_mutants_of_a_generic_chain_of_n_additions_scales() {
    on_main_sized_stack(|| running_a_chain("generic ", 50, generic_chain_with_row));
}

fn running_a_chain(kind: &str, n: usize, make: fn(usize) -> String) {
    let cache = Warm::default();
    // n mutants, each O(n) to build, remix and run: order 2.
    scaling::check_order(
        &format!("running the mutants of a {kind}chain of n additions"),
        n,
        2,
        |n| {
            let (text, mut db) = warm(&cache, n, make);
            let front = db.front(&text);
            let (stmts, unit, _) = front.as_ref().as_ref().unwrap();
            let found = mutate::run(&text, stmts, unit, &run::direct).unwrap();
            assert_eq!(found.len(), 3 * n);
            // Each mutant changes the sum, and the row detects it.
            assert!(found.iter().all(|(_, v)| *v == Verdict::Detected));
        },
    );
}
