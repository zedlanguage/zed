//! Step L1.39b: the derivation of a rejection and the exact preimage of `@exact` are built
//! only when asked for (DESIGN.md sec:plan, "Optional properties are computed on demand",
//! items 4 and 6). A check counts the parts of derivations it builds and a search the boxes it
//! takes; a check that reports no rejection builds none, and one rejection of a fixed size
//! costs the same in a program of n functions as in one of 8n.

mod exact;

use std::collections::HashMap;

use zed_tests::{oracle, scaling};
use zedc::check::derivation_steps;
use zedc::run::load;
use zedc::store::preimage::exact_steps;

/// The stack each check here runs on, as deep as the corpus's deepest program needs.
const STACK: usize = 1 << 28;

/// Whether `src` loads, and the parts of derivations its check built.
fn counted(src: &str) -> (Result<(), String>, u64) {
    derivation_steps();
    let r = load(src.as_bytes()).map(|_| ());
    (r, derivation_steps())
}

/// `n` functions, each with a declared parameter, a binding and a call of the first one,
/// and a `main` that calls the last: every kind of origin a check records, and no rejection.
fn clean(n: usize) -> String {
    let mut src = String::from("g0(positional x: int) = x + 1;\n");
    for i in 1..n {
        src += &format!("g{i}(positional x: int) = {{\n  y = x * 2;\n  return g0(y);\n}};\n");
    }
    src + &format!(
        "main(stdin: Lines) -> (stdout: Lines) {{\n  a = g{}(1);\n  stdout <- \"a\" ++ String(a);\n}}\n",
        n - 1
    )
}

/// [`clean`] with one function whose condition is no `bool`: a rejection of a fixed size.
fn one_rejection(n: usize) -> String {
    clean(n) + "bad(positional x: int) = if x { 1 } else { 2 };\n"
}

#[test]
fn the_program_of_n_functions_is_accepted_and_the_one_with_a_bad_condition_is_not() {
    scaling::on_a_thread(STACK, || {
        assert_eq!(counted(&clean(3)), (Ok(()), 0));
        let (r, built) = counted(&one_rejection(3));
        let out = r.expect_err("a condition of int is rejected");
        assert!(
            out.contains("the condition of `if` is int, not bool"),
            "{out}"
        );
        assert!(out.contains("`x` is declared `int`"), "{out}");
        // The counter counts: the reported derivation was built.
        assert!(built > 0);
    });
}

#[test]
fn a_corpus_unit_with_no_rejection_builds_no_derivation() {
    scaling::on_a_thread(STACK, || {
        let units = oracle::corpus().into_iter().map(|(p, _)| p);
        let (mut accepted, mut rejected) = (0, 0);
        for path in units.chain(oracle::step_units()) {
            let Ok(text) = std::fs::read_to_string(&path) else {
                continue;
            };
            derivation_steps();
            exact_steps();
            match load(text.as_bytes()) {
                Ok(_) => {
                    accepted += 1;
                    assert_eq!(derivation_steps(), 0, "{}", path.display());
                    assert_eq!(exact_steps(), 0, "{}", path.display());
                }
                Err(_) => rejected += 1,
            }
        }
        // Most corpus units use constructs compiled from later steps and are rejected before
        // or by the check, which reports each rejection with its derivation.
        assert!(accepted > 0, "{accepted} accepted, {rejected} rejected");
        eprintln!("{accepted} accepted, {rejected} rejected");
    });
}

#[test]
fn one_rejection_builds_the_same_derivation_among_n_functions_as_among_8n() {
    scaling::on_a_thread(STACK, || {
        let (r, small) = counted(&one_rejection(50));
        let small_out = r.expect_err("rejected");
        let (r, large) = counted(&one_rejection(400));
        let large_out = r.expect_err("rejected");
        assert!(small > 0);
        assert_eq!(small, large);
        // The same rejection, printed the same, but for its line.
        let tail = |s: &str| s.lines().skip(1).filter(|l| !l.contains(':')).count();
        assert_eq!(tail(&small_out), tail(&large_out));
    });
}

#[test]
fn checking_functions_that_ask_for_no_derivation_scales() {
    // The sources are built before the runs are measured.
    let n = 300;
    let srcs: HashMap<usize, String> = [n, 8 * n].into_iter().map(|k| (k, clean(k))).collect();
    scaling::check_order("checking n functions with no rejection", n, 1, |k| {
        let src = &srcs[&k];
        assert!(load(src.as_bytes()).is_ok());
        assert_eq!(derivation_steps(), 0);
    });
}
