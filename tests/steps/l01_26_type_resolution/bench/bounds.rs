use zedc::ast::unit;
use zedc::check::read::parse_type;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};
use zedc::resolve::resolve;
use zed_tests::step_helpers::l01_13_formatter::fmt;

use super::super::bounds::{
    bounded_chain, distinct_bounds_chain, many_bounds, nested, nested_lambdas, passed,
    passed_deep, shared_bounded_chain, wide, wide_lambda,
};
use super::super::info;

/// The types of `many_bounds` at `n` and `8n` and their printed texts, built before timing.
fn signatures_of_many_bounds(
    n: usize,
) -> std::collections::HashMap<usize, (zedc::check::ty::Ty, String)> {
    [n, zed_tests::scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let t = parse_type(&many_bounds(m)).unwrap_or_else(|e| panic!("{e}"));
            let text = t.to_string();
            (m, (t, text))
        })
        .collect()
}

#[test]
fn printing_a_signature_of_many_bounds_scales() {
    let n = 400;
    let inputs = signatures_of_many_bounds(n);
    zed_tests::scaling::check("printing a signature of n bounds", n, |m| {
        let (t, _) = &inputs[&m];
        assert_eq!(t.to_string().matches(" in ").count(), m);
    });
}

#[test]
fn reading_back_a_signature_of_many_bounds_scales() {
    let n = 400;
    let inputs = signatures_of_many_bounds(n);
    zed_tests::scaling::check("reading back a signature of n bounds", n, |m| {
        let (t, text) = &inputs[&m];
        assert_eq!(&parse_type(text).unwrap_or_else(|e| panic!("{e}")), t);
    });
}
/// The unit `text` lexed, parsed and resolved, for a test that times the check alone.
fn resolved(text: &str) -> (Vec<zedc::ast::Stmt>, zedc::resolve::Resolution) {
    let tokens = lex_fence(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap();
    let stmts = unit(text, &tokens, &tree).unwrap();
    let res = resolve(&stmts).unwrap_or_else(|e| panic!("{e:?}"));
    (stmts, res)
}

/// Checks `make(n)` at `n` and `8n` with `check_order`, each input lexed, parsed and resolved
/// before timing, so that the check alone is measured.
fn check_scales(what: &str, n: usize, make: impl Fn(usize) -> String) {
    let inputs: std::collections::HashMap<usize, _> = [n, zed_tests::scaling::FACTOR * n]
        .into_iter()
        .map(|n| (n, resolved(&make(n))))
        .collect();
    zed_tests::scaling::check_order(what, n, 1, |n| {
        let (stmts, res) = &inputs[&n];
        let info = zedc::check::walk::check(stmts, res);
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

#[test]
fn many_bounded_variables_scale() {
    assert_eq!(fmt(&wide(800)), wide(800));
    check_scales("a clause of n bounds and a call of n arguments", 800, wide);
}

#[test]
fn passing_a_function_of_many_bounded_variables_scales() {
    check_scales(
        "a function of n bounded variables passed as one of n",
        800,
        passed,
    );
}

#[test]
fn nested_bounds_clauses_scale() {
    // On the test thread's stack: `Denote::ty` (zedc-check) recursed on the nesting of a
    // written type and overflowed 2 MiB here; it keeps its own stack (TY-write-stack).
    assert_eq!(fmt(&nested(400)), nested(400));
    // The check alone is timed: the formatter's linear work would hide a walk of each
    // clause's whole type, quadratic in the depth.
    check_scales("n nested bounds clauses", 400, nested);
}

#[test]
fn printing_a_deep_function_type_scales() {
    // Each function type is written in place: building each part as a string and copying it
    // into the whole cost O(n^2) for n nested function types.
    // On the test thread's stack: `Denote::ty` (zedc-check) recursed on the nesting of a
    // written type and overflowed 2 MiB here; it keeps its own stack (TY-write-stack).
    let inputs: std::collections::HashMap<usize, _> = [800, 6400]
        .into_iter()
        .map(|n| {
            let (info, names) = info(&nested(n));
            let (_, s) = info
                .sigs
                .iter()
                .find(|(id, _)| names[**id] == "h")
                .expect("h");
            (n, s.clone())
        })
        .collect();
    assert!(inputs[&800].to_string().ends_with(" -> 0"));
    zed_tests::scaling::check("printing n nested function types", 800, |n| {
        assert!(!inputs[&n].to_string().is_empty());
    });
}

#[test]
fn passing_a_deep_function_type_as_itself_scales() {
    // On the test thread's stack: `Denote::ty` (zedc-check) recursed on the nesting of a
    // written type and overflowed 2 MiB here; it keeps its own stack (TY-write-stack).
    check_scales("a function type n deep passed as itself", 400, |n| {
        passed_deep(n, false)
    });
}

#[test]
fn passing_a_deep_bounded_function_type_as_itself_scales() {
    // On the test thread's stack: `Denote::ty` (zedc-check) recursed on the nesting of a
    // written type and overflowed 2 MiB here; it keeps its own stack (TY-write-stack).
    check_scales(
        "a function type n deep, a bound at each level, passed as itself",
        400,
        |n| passed_deep(n, true),
    );
}

#[test]
fn a_lambda_of_many_bounded_parameters_scales() {
    check_scales(
        "a lambda of n bounded parameters passed as a function of n",
        800,
        wide_lambda,
    );
}

#[test]
fn nested_lambdas_for_bounded_parameters_scale() {
    zed_tests::deep::on_small_stack(|| {
        check_scales(
            "n nested lambdas, each for a bounded parameter",
            400,
            nested_lambdas,
        );
    });
}

#[test]
fn reading_a_chain_of_shared_bounded_parts_scales() {
    let n = 200;
    let texts: std::collections::HashMap<usize, String> = [n, zed_tests::scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, shared_bounded_chain(m)))
        .collect();
    zed_tests::scaling::check("reading a chain of n shared bounded tuples", n, |m| {
        let t = parse_type(&texts[&m]).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(t.tuples.len(), 1);
    });
}

#[test]
fn reading_a_chain_of_bounded_definitions_scales() {
    let n = 200;
    let texts = zed_tests::scaling::inputs(n, bounded_chain);
    zed_tests::scaling::check_order(
        "reading a chain of n definitions, each with its own bounds clause",
        n,
        1,
        |m| {
            let t = parse_type(&texts[&m]).unwrap_or_else(|e| panic!("{e}"));
            assert_eq!(t.tuples.len(), 1);
        },
    );
}

#[test]
fn reading_back_a_printed_type_of_many_distinct_bounded_variables_scales() {
    // The printed texts of `distinct_bounds_chain`, built before timing. Each of the n clauses
    // bounds a variable of its own name on a signature of the last part, which the reading
    // meets first: O(n). A reading that searched the type for each variable, as it does for
    // a variable whose signature was emptied away, would take O(n^2) here (COMPLEXITY.md
    // F155).
    let n = 200;
    let inputs = zed_tests::scaling::inputs(n, |m| {
        let t = parse_type(&distinct_bounds_chain(m)).unwrap_or_else(|e| panic!("{e}"));
        let text = t.to_string();
        (t, text)
    });
    zed_tests::scaling::check(
        "reading back a printed type of n bounded signatures, each for a variable of its own name",
        n,
        |m| {
            let (t, text) = &inputs[&m];
            assert_eq!(&parse_type(text).unwrap_or_else(|e| panic!("{e}")), t);
        },
    );
}
