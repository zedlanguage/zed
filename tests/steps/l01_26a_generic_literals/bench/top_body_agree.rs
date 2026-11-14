use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

use super::super::top_body_agree::{comparisons, nested_int_exponents, powers};

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
