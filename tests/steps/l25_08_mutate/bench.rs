//! The rule of low complexity (DESIGN.md Part G): finding the mutants reads each node once,
//! and a mutant costs its definition and the rows that reach it, not the unit. The benchmarks
//! of this step, run by `tools/run_tests.sh --bench`; what each asserts besides its ratio is
//! checked at small sizes by `scaling::the_mutants_of_each_benchmark_unit_at_small_sizes`.

use std::sync::{Arc, Mutex};

use zed_tests::deep::on_main_sized_stack;
use zed_tests::scaling;
use zedc::query::Db;
use zedc::stage::{self, Remix};

use super::scaling::{
    Warm, chain, chain_with_row, finds_the_mutants, generic_chain_with_row, remixes_to_a_lambda,
    runs_the_mutants_of_a_chain, runs_the_mutants_of_functions, unit, warm,
};

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
            let (text, db) = warm(&cache, n, make);
            finds_the_mutants(&text, db, per * n);
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
            let (text, db) = warm(&cache, n, unit);
            runs_the_mutants_of_functions(&text, db, n);
        },
    );
}

#[test]
fn running_the_mutants_of_a_chain_of_n_additions_scales() {
    // The front end elaborates a chain by recursion, as deep as the chain: a main thread's stack.
    on_main_sized_stack(|| running_a_chain("", 100, chain_with_row));
}

#[test]
fn running_the_mutants_of_a_generic_chain_of_n_additions_scales() {
    // At 50 and 400 it took 18.3 s at load 19 and past 22 s at load 34, and at 35 and 280 15.6 s
    // at load 39 (ratio 56.6 by instructions); the work is order 2, so 25 and 200 do half that.
    on_main_sized_stack(|| running_a_chain("generic ", 25, generic_chain_with_row));
}

fn running_a_chain(kind: &str, n: usize, make: fn(usize) -> String) {
    let cache = Warm::default();
    // n mutants, each O(n) to build, remix and run: order 2.
    scaling::check_order(
        &format!("running the mutants of a {kind}chain of n additions"),
        n,
        2,
        |n| {
            let (text, db) = warm(&cache, n, make);
            runs_the_mutants_of_a_chain(&text, db, n);
        },
    );
}

#[test]
fn remixing_a_definition_costs_less_than_mixing_it() {
    // `Remix::mix` mixes a term of a definition as `mix` mixes the definition, with the
    // set-up already done: it is the mixing part of `mix`'s work, without the reads of each
    // definition's free names. A mutant of a generic chain of 400 additions remixed in 32.8M
    // instructions against 52.1M for `mix` of the definition, 0.63 times. Reading the free
    // names of the term and of the mixed term again, by two fresh walks (`stage::free`),
    // cost 45.0M, 0.86 times, and 18% more for the mutants of the chain (plan row
    // TEST-mutate-generic-time, COMPLEXITY.md F161); the limit lies between. That the two
    // give the same term is checked at small sizes in `scaling.rs`.
    on_main_sized_stack(|| {
        let text = generic_chain_with_row(400);
        let mut db = Db::new();
        let front = db.front(&text);
        let (_, unit, _) = front.as_ref().as_ref().unwrap();
        let term = &unit.defs[0].term;
        let (_, remix) = Remix::new(unit);
        let remix = Mutex::new(remix);
        scaling::compare_costs(
            "Remix::mix against mix of a generic chain of 400 additions",
            "Remix::mix mixes the term without mix's reads of each definition's free names",
            0.75,
            || {
                stage::mix(unit, &["f"]);
            },
            || {
                remix.lock().unwrap().mix(term);
            },
        );
    });
}

#[test]
fn remixing_a_generic_chain_of_n_additions_scales() {
    // One remix of the definition: its mixing, and the cut reads taken from the mixer's own
    // summaries, each O(n) (TEST-mutate-generic-time).
    on_main_sized_stack(|| {
        let made = scaling::inputs(100, |n| {
            let text = generic_chain_with_row(n);
            let mut db = Db::new();
            let front = db.front(&text);
            let (_, unit, _) = front.as_ref().as_ref().unwrap();
            let (_, remix) = Remix::new(unit);
            (Arc::clone(unit), Mutex::new(remix))
        });
        scaling::check("Remix::mix of a generic chain of n additions", 100, |n| {
            let (unit, remix) = &made[&n];
            remixes_to_a_lambda(unit, remix);
        });
    });
}
