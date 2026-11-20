use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

use super::super::top_body_agree::{
    comparisons, display_ops, generic_ops, nested_int_exponents,
    nested_powers_by_an_inexact_divisor, powers,
};

/// `n` top-level calls, each giving an operation on literals alone to a generic parameter or
/// to `min` beside a decimal, and one call each whose operation is a sum of `n` divisions:
/// each call reads its arguments once (`Ck::lit_ops_meet`, `Ck::min_max_lit_ops`), and each
/// operation is read once at a carrier (`Ck::lit_fit`) and walked once more as it takes it
/// (`Ck::lit_takes`), O(size of the line) per line, O(n) in all (row
/// FAIL-top-literal-op-at-generic-arg).
///
/// Besides its ratio: no error. Small instance:
/// `top_body_agree::many_operations_at_generic_arguments_take_f64`.
#[test]
fn operations_at_generic_arguments_scale() {
    scaling::on_a_thread(1 << 29, || {
        let n = 300;
        let srcs = [generic_ops(n), generic_ops(scaling::FACTOR * n)];
        assert_eq!(type_errors(&srcs[0]), Vec::<String>::new());
        scaling::check(
            "checking n operations on literals at generic arguments",
            n,
            |m| {
                type_errors(&srcs[usize::from(m != n)]);
            },
        );
    });
}

#[test]
fn comparisons_in_a_body_are_checked_in_linear_time() {
    scaling::on_a_thread(1 << 29, || {
        let n = 1000;
        let srcs = [comparisons(n), comparisons(scaling::FACTOR * n)];
        scaling::check(
            "checking a body of n comparisons of operations on literals alone",
            n,
            |m| {
                type_errors(&srcs[usize::from(m != n)]);
            },
        );
    });
}

#[test]
fn a_top_level_line_of_many_powers_takes_f64_in_linear_time() {
    scaling::on_a_thread(1 << 29, || {
        let n = 500;
        let srcs = [powers(n), powers(scaling::FACTOR * n)];
        scaling::check(
            "checking a top-level line of n powers that take f64",
            n,
            |m| {
                type_errors(&srcs[usize::from(m != n)]);
            },
        );
    });
}

#[test]
fn nested_int_operation_exponents_are_read_in_linear_time() {
    // Each `^` reads its exponent as an `int` (plan row LIT-rat-int-op-exponent): read anew
    // at each of the n powers, as the text walk does, that is O(n^2); kept by operation, and
    // not entered again at the top level, O(n). The correctness test is
    // `top_body_agree::nested_int_operation_exponents_take_rat`.
    scaling::on_a_thread(1 << 29, || {
        let n = 2000;
        let srcs = [
            nested_int_exponents(n),
            nested_int_exponents(scaling::FACTOR * n),
        ];
        scaling::check("checking n nested int exponents", n, |m| {
            type_errors(&srcs[usize::from(m != n)]);
        });
    });
}

#[test]
fn nested_powers_by_an_inexact_divisor_are_rejected_in_linear_time() {
    // The menu drops the `f64` forms where a literal they leave is no exact `f64`, testing
    // each literal against a set of the rewritten ones: O(l) for l literals, where searching
    // the rewritten ones for each is O(l^2). The correctness test is
    // `top_body_agree::nested_powers_by_an_inexact_divisor_offer_no_f64_form`.
    scaling::on_a_thread(1 << 29, || {
        let n = 500;
        let srcs = [
            nested_powers_by_an_inexact_divisor(n),
            nested_powers_by_an_inexact_divisor(scaling::FACTOR * n),
        ];
        scaling::check(
            "checking n nested powers by a divisor no f64 holds",
            n,
            |m| {
                type_errors(&srcs[usize::from(m != n)]);
            },
        );
    });
}

/// One top-level array of `n` parts that take `f64` inside tuples, atoms, sets and maps, and
/// one array nested `n` deep around such a part: the parts are found in one walk of the value
/// (`top_f64_leaves`), each takes `f64` once (`Ck::lit_takes`), and the value's type is made
/// again in one walk (`retyped`, one lookup per part), O(size of the value).
///
/// Besides its ratio: no error. Small instance:
/// `top_body_agree::a_display_of_many_parts_that_take_f64_is_accepted`.
#[test]
fn displays_with_parts_that_take_f64_scale() {
    scaling::on_a_thread(1 << 29, || {
        let n = 400;
        let srcs = [display_ops(n), display_ops(scaling::FACTOR * n)];
        assert_eq!(type_errors(&srcs[0]), Vec::<String>::new());
        scaling::check(
            "checking a top-level display of n parts that take f64",
            n,
            |m| {
                type_errors(&srcs[usize::from(m != n)]);
            },
        );
    });
}
