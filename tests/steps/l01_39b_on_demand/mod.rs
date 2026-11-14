//! Step L1.39b: the derivation of a rejection and the exact preimage of `@exact` are built
//! only when asked for (DESIGN.md sec:plan, "Optional properties are computed on demand",
//! items 4 and 6). A check counts the parts of derivations it builds and a search the boxes it
//! takes; a check that reports no rejection builds none, and one rejection of a fixed size
//! costs the same in a program of n functions as in one of 8n.

mod bench;
mod completeness;
mod exact;

use zed_tests::{oracle, scaling};
use zedc::check::derivation_steps;
use zedc::run::load;
use zedc::store::preimage::exact_steps;

/// The stack each check here runs on, as deep as the corpus's deepest program needs.
pub(crate) const STACK: usize = 1 << 28;

/// Whether `src` loads, and the parts of derivations its check built.
pub(crate) fn counted(src: &str) -> (Result<(), String>, u64) {
    derivation_steps();
    let r = load(src.as_bytes()).map(|_| ());
    (r, derivation_steps())
}

/// `n` functions, each with a declared parameter, a binding and a call of the first one,
/// and a `main` that calls the last: every kind of origin a check records, and no rejection.
pub(crate) fn clean(n: usize) -> String {
    let mut src = String::from("g0(positional x: int) = x + 1;\n");
    for i in 1..n {
        src += &format!("g{i}(positional x: int) = {{\n  y = x * 2;\n  return g0(y);\n}};\n");
    }
    src + &format!(
        "main(m: MainArgs) {{\n  a = g{}(1);\n  m.stdout <- \"a\" ++ String(a);\n}}\n",
        n - 1
    )
}

/// [`clean`] with one function whose condition is no `bool`: a rejection of a fixed size.
pub(crate) fn one_rejection(n: usize) -> String {
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
fn functions_of_many_parameters_are_accepted_with_no_derivation() {
    // The small instance of `bench::checking_functions_of_many_parameters_scales`.
    scaling::on_a_thread(STACK, || {
        assert_eq!(counted(&many_parameters(3, 40)), (Ok(()), 0));
        let stmts = zed_tests::deep::statements(&many_parameters(3, 40));
        let res = zedc::resolve::resolve(&stmts).expect("resolves");
        let info = zedc::check::walk::check(&stmts, &res);
        assert!(info.errors.is_empty(), "{:?}", info.errors);
        assert_eq!(derivation_steps(), 0);
    });
}

/// `n` functions of `m` declared parameters each, returning the last, and a `main` that calls
/// the first: many binders, each of which costs the checker little beyond its origin.
pub(crate) fn many_parameters(n: usize, m: usize) -> String {
    let params = (0..m)
        .map(|j| format!("p{j}: int"))
        .collect::<Vec<_>>()
        .join(", ");
    let mut src = String::new();
    for i in 0..n {
        src += &format!("g{i}({params}) = p{};\n", m - 1);
    }
    let args = (0..m)
        .map(|j| format!("p{j}: 1"))
        .collect::<Vec<_>>()
        .join(", ");
    src + &format!(
        "main(m: MainArgs) {{\n  a = g0({args});\n  m.stdout <- \"a\" ++ String(a);\n}}\n"
    )
}
