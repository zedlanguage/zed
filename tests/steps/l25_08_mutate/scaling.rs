//! The inputs of the mutation benchmarks in `bench.rs` (DESIGN.md Part G: finding the mutants
//! reads each node once, and a mutant costs its definition and the rows that reach it, not the
//! unit), and what each benchmark asserts besides its ratio, checked here at small sizes
//! (TEST-bench-move-rest, P170).

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use zed_kernel::Term;
use zedc::elab::Unit;
use zedc::mutate::{self, Verdict};
use zedc::query::Db;
use zedc::run;
use zedc::stage::{self, Remix};

/// `n` functions, each with one operator, one constant and a row of its own, beside a table
/// of fixed size: `3n + 3` mutants, each of which runs the one row that reaches its
/// definition, so the run measures what a mutant's rows cost.
pub(super) fn unit(n: usize) -> String {
    let mut text =
        String::from("isChild(positional age) = age <= 12 test { 12 -> true, 13 -> false }\n");
    for i in 0..n {
        text += &format!("g{i}(positional x) = x + {i} test {{ 0 -> {i} }}\n");
    }
    text
}

/// One definition with `n` additions in a chain: `x + 1 + 1 + …`, `2n` operator and constant
/// nodes, nested `n` deep.
pub(super) fn chain(n: usize) -> String {
    format!("f(positional x) = x{};\n", " + 1".repeat(n))
}

/// The front end's result for each size, made once, so that only the mutants are timed.
pub(super) type Warm = Mutex<BTreeMap<usize, (String, Db)>>;

pub(super) fn warm(warm: &Warm, n: usize, make: fn(usize) -> String) -> (String, Db) {
    let mut warm = warm.lock().unwrap();
    let (text, db) = warm.entry(n).or_insert_with(|| {
        let text = make(n);
        let mut db = Db::new();
        db.front(&text);
        (text, db)
    });
    (text.clone(), db.clone())
}

/// One definition with `n` additions in a chain and a row that checks its sum: `3n` mutants
/// (each `+` by `-`, each `1` by `0` and by `2`), each of which copies, remixes and runs the
/// whole definition, so the run is of order n². `x` is declared `int`, so each `1` is an `int`.
pub(super) fn chain_with_row(n: usize) -> String {
    format!(
        "f(positional x: int) = x{} test {{ 0 -> {n} }}\n",
        " + 1".repeat(n)
    )
}

/// [`chain_with_row`] with `x` undeclared: each `1` takes the carrier of `x` (DESIGN.md L1.26a),
/// one `match` on it per literal, and each mutant runs about 6 times the work of the `int`
/// chain's (COMPLEXITY.md F135).
pub(super) fn generic_chain_with_row(n: usize) -> String {
    format!(
        "f(positional x) = x{} test {{ 0 -> {n} }}\n",
        " + 1".repeat(n)
    )
}

/// At least `at_least` mutants are found in `text`.
pub(super) fn finds_the_mutants(text: &str, mut db: Db, at_least: usize) {
    let front = db.front(text);
    let (stmts, unit, _) = front.as_ref().as_ref().unwrap();
    let found = mutate::mutants(text, stmts, unit).unwrap();
    assert!(found.len() >= at_least, "{}", found.len());
}

/// The `3n + 3` mutants of [`unit`]`(n)` each ran their row; only `x + 0` replaced by `x - 0` in
/// `g0` passes it.
pub(super) fn runs_the_mutants_of_functions(text: &str, mut db: Db, n: usize) {
    let front = db.front(text);
    let (stmts, unit, _) = front.as_ref().as_ref().unwrap();
    let found = mutate::run(text, stmts, unit, &run::direct).unwrap();
    assert_eq!(found.len(), 3 * n + 3);
    let detected = found
        .iter()
        .filter(|(_, v)| *v == Verdict::Detected)
        .count();
    assert_eq!(detected, 3 * n + 2);
}

/// The `3n` mutants of a chain of `n` additions with a row each change the sum, and the row
/// detects each.
pub(super) fn runs_the_mutants_of_a_chain(text: &str, mut db: Db, n: usize) {
    let front = db.front(text);
    let (stmts, unit, _) = front.as_ref().as_ref().unwrap();
    let found = mutate::run(text, stmts, unit, &run::direct).unwrap();
    assert_eq!(found.len(), 3 * n);
    assert!(found.iter().all(|(_, v)| *v == Verdict::Detected));
}

/// One remix of the first definition of `unit` gives a function.
pub(super) fn remixes_to_a_lambda(unit: &Arc<Unit>, remix: &Mutex<Remix>) {
    let out = remix.lock().unwrap().mix(&unit.defs[0].term);
    assert!(matches!(out, Term::Lam(..)), "{out}");
}

/// Each benchmark of `bench.rs` at small sizes, through the same assertions: the mutants found
/// in [`unit`] and [`chain`], the verdicts of the mutants run on [`unit`], [`chain_with_row`] and
/// [`generic_chain_with_row`], a remix of the generic chain, and that `Remix::mix` gives the
/// term `mix` gives, which `remixing_a_definition_costs_less_than_mixing_it` times at 400.
#[test]
fn the_mutants_of_each_benchmark_unit_at_small_sizes() {
    for n in [1, 2, 9] {
        let cache = Warm::default();
        let (text, db) = warm(&cache, n, unit);
        finds_the_mutants(&text, db.clone(), 3 * n);
        runs_the_mutants_of_functions(&text, db, n);
        let (text, db) = warm(&cache, n, chain);
        finds_the_mutants(&text, db, 3 * n);
        for make in [
            chain_with_row as fn(usize) -> String,
            generic_chain_with_row,
        ] {
            let cache = Warm::default();
            let (text, db) = warm(&cache, n, make);
            runs_the_mutants_of_a_chain(&text, db, n);
        }
        let text = generic_chain_with_row(n);
        let mut db = Db::new();
        let front = db.front(&text);
        let (_, unit, _) = front.as_ref().as_ref().unwrap();
        let (_, remix) = Remix::new(unit);
        let remix = Mutex::new(remix);
        assert_eq!(
            remix.lock().unwrap().mix(&unit.defs[0].term).to_string(),
            stage::mix(unit, &["f"]).0.defs[0].term.to_string()
        );
        remixes_to_a_lambda(unit, &remix);
    }
}
