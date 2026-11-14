//! The benchmarks of the catalog tool, run by `tools/run_tests.sh --bench`: the Zed check of a
//! catalog cell is linear in the nesting of its lambdas and in its text, and the scan of an
//! index is linear in its documents. What each asserts besides its ratio is checked at small
//! sizes by `nested_lambdas_and_chains_of_calls_pass_the_zed_check` and
//! `the_scan_of_many_documents_finds_each_routine_once`.

use std::collections::HashSet;

use zed_tests::scaling::{check, inputs};
use zed_tools::catalog::check_zed;
use zed_tools::layer::WordTable;
use zed_tools::spec::Spec;

use super::{call_chain, many_documents, nested_lambdas, ours, scan_finds_each_routine, spec_dir};

/// The scope of lambda parameters costs no walk up a name's ancestors: lambdas nested `n` deep,
/// whose innermost body reads the outermost lambda's parameter and the innermost one's `n`
/// times each, are checked in time linear in `n`.
#[test]
fn check_zed_scales_linearly_with_lambda_nesting() {
    let dir = spec_dir("catalog_zed_nesting");
    let spec = Spec::open(&dir.root()).expect("the test spec");
    let words = WordTable::read(&spec.design).expect("its table");
    let rows = HashSet::new();
    let texts = inputs(1000, nested_lambdas);
    check("catalog check of n nested lambdas", 1000, |n| {
        assert_eq!(check_zed(&texts[&n], &spec, &words, &rows), None);
    });
}

/// The words-and-arguments check is linear in the text: a chain of `n` calls, each with a lambda
/// and a named argument.
#[test]
fn check_zed_scales_linearly_with_the_text() {
    let dir = spec_dir("catalog_zed_scaling");
    let spec = Spec::open(&dir.root()).expect("the test spec");
    let words = WordTable::read(&spec.design).expect("its table");
    let rows = HashSet::new();
    let texts = inputs(500, call_chain);
    check("catalog check of a chain of n calls", 500, |n| {
        assert_eq!(check_zed(&texts[&n], &spec, &words, &rows), None);
    });
}

/// The scan of an index of n documents, each with eight uses of routines out of n / 2.
#[test]
fn scan_scales_linearly_with_the_index() {
    let o = ours();
    let built = inputs(2_000, many_documents);
    check("catalog scan of n documents", 2_000, |n| {
        scan_finds_each_routine(&built[&n], n, &o);
    });
}
