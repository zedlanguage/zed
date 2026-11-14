use zed_tests::scaling;
use zed_tests::step_helpers::l01_16_elaboration::checked;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

use super::super::tuple_arg_pair::{branches, chain, decimals, deep, picks, shared};

/// Checks `src(m)` at `n` and `8n`, each accepted with no error.
fn accepted(what: &str, n: usize, src: impl Fn(usize) -> String + Sync) {
    scaling::on_a_thread(1 << 29, || {
        let srcs = [src(n), src(scaling::FACTOR * n)];
        scaling::check(what, n, |m| {
            assert_eq!(
                type_errors(&srcs[usize::from(m != n)]),
                Vec::<String>::new()
            );
        });
    });
}

/// Checks and elaborates `make(m)` at `n` and `8n`.
fn elaborated(what: &str, n: usize, make: fn(usize) -> String) {
    scaling::on_a_thread(1 << 29, || {
        let srcs = [make(n), make(scaling::FACTOR * n)];
        scaling::check(what, n, |m| {
            let c = checked(&srcs[usize::from(m != n)]);
            c.elab();
        });
    });
}

#[test]
fn many_decimal_components_check_in_linear_time_each_added() {
    accepted(
        "checking a call of n decimal components, each added to 1r",
        100,
        |m| decimals(m, false),
    );
}

#[test]
fn many_decimal_components_check_in_linear_time_summed() {
    accepted(
        "checking a call of n decimal components summed",
        100,
        |m| decimals(m, true),
    );
}

#[test]
fn many_components_and_nested_calls_check_in_linear_time_components() {
    accepted("checking a call of n literal components", 100, picks);
}

#[test]
fn many_components_and_nested_calls_check_in_linear_time_nested_calls() {
    accepted("checking n nested calls of a pair of literals", 40, chain);
}

#[test]
fn many_branches_beside_components_check_and_elaborate_in_linear_time_components() {
    elaborated(
        "checking and elaborating n literal branches beside n components",
        100,
        branches,
    );
}

#[test]
fn many_branches_beside_components_check_and_elaborate_in_linear_time_a_deep_read() {
    elaborated(
        "checking and elaborating a literal branch beside a read n deep",
        60,
        deep,
    );
}

#[test]
fn many_branches_beside_components_check_and_elaborate_in_linear_time_one_component() {
    elaborated(
        "checking and elaborating n literal branches beside reads of one component",
        100,
        shared,
    );
}
