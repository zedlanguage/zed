//! A function argument fits the function type its slot expects: by its parameters' names,
//! in any order; a lambda by its own names; a parameter the type leaves out only with a
//! default.

use super::{info, type_errors};
use crate::l01_16_elaboration::value;
use zedc::check::Fit;

const APPLY: &str = "apply(f: (a: int, b: int) -> int) = f(a: 1, b: 2);\n";

fn fits(text: &str) -> Vec<Fit> {
    info(text).0.fits.into_values().collect()
}

#[test]
fn a_function_with_the_same_names_in_order_needs_no_fit() {
    let p = format!("{APPLY}sub(a, b) = a - b;\ny = apply(f: sub);\n");
    assert!(fits(&p).is_empty());
    assert_eq!(value(&p, "y"), "-1");
}

#[test]
fn a_function_with_the_names_reordered_gets_an_adapter() {
    let p = format!("{APPLY}sub(b, a) = a - b;\ny = apply(f: sub);\n");
    assert_eq!(fits(&p), [Fit::Adapter { from: vec![1, 0] }]);
    assert_eq!(value(&p, "y"), "-1");
}

#[test]
fn a_lambda_takes_its_parameters_by_name() {
    let p = format!("{APPLY}y = apply(f: (b, a) -> a - b);\n");
    assert_eq!(
        fits(&p),
        [Fit::Lambda {
            order: vec![Some(1), Some(0)],
            extra: vec![]
        }]
    );
    assert_eq!(value(&p, "y"), "-1");
}

#[test]
fn a_lambda_parameter_the_type_leaves_out_takes_its_default() {
    let p = "apply(f: (a: int) -> int) = f(a: 3);\ny = apply(f: (a, k = 10) -> a * k);\n";
    assert_eq!(value(p, "y"), "30");
}

#[test]
fn a_lambda_parameter_with_another_name_is_an_error() {
    assert_eq!(
        type_errors(&format!("{APPLY}y = apply(f: (a, s) -> a - s);\n")),
        [
            "the lambda's parameter `s` is not a parameter of `(a: int, b: int) -> int`: \
          rename it `b` [s]"
        ]
    );
}

#[test]
fn named_parameters_do_not_fit_a_positional_type() {
    assert_eq!(
        type_errors(
            "apply(f: (int, int) -> int) = f(1, 2);\nsub(a, b) = a - b;\ny = apply(f: sub);\n"
        ),
        [
            "the parameters of `sub` (a, b) do not fit `(int, int) -> int`: declare them as it \
          passes them, with `positional` where it passes by position, or pass a lambda, \
          (a, b) -> sub(a: a, b: b) [sub]"
        ]
    );
}

#[test]
fn a_lambdas_result_must_fit() {
    assert_eq!(
        type_errors("apply(f: (int) -> String) = f(1);\ny = apply(f: n -> n + 1);\n"),
        ["the lambda returns int, and `(int) -> String` returns String [n + 1]"]
    );
}
