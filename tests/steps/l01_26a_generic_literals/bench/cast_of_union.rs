//! A cast splits the values of the call among the arrows, or reads the body for the `2.5`, or
//! tries the four wraps as written: linear in the values, at each cast. Small instances:
//! `casts_of_a_call_of_many_values_take_each_value_at_its_arrow`.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::Resolved;

use super::super::cast_of_union::many;

/// Checks `word(g(0))` with `g` of `n` values and `last`, at `n = 200` and `8n`.
fn one_cast_of_many_values(last: &str, word: &str) {
    scaling::on_a_thread(1 << 28, || {
        let n = 200;
        let units = scaling::inputs(n, |m| Resolved::new(&many(m, 1, last, word)));
        scaling::check(
            &format!("checking `{word}(g(0))`, `g` of n values and {last}"),
            n,
            |m| {
                units[&m].check();
            },
        );
    });
}

/// Checks `n` casts `word(g(k))` with `g` of two values and `last`, at `n = 200` and `8n`.
fn many_casts_of_two_values(last: &str, word: &str) {
    scaling::on_a_thread(1 << 28, || {
        let n = 200;
        let units = scaling::inputs(n, |m| Resolved::new(&many(2, m, last, word)));
        scaling::check(
            &format!("checking n casts `{word}(g(k))`, `g` of two values and {last}"),
            n,
            |m| {
                units[&m].check();
            },
        );
    });
}

#[test]
fn casts_of_a_call_of_many_values_check_in_linear_time_f64_of_a_suffixed_value() {
    one_cast_of_many_values("2.5f64", "f64");
}

#[test]
fn casts_of_a_call_of_many_values_check_in_linear_time_many_casts_f64_of_a_suffixed_value() {
    many_casts_of_two_values("2.5f64", "f64");
}

#[test]
fn casts_of_a_call_of_many_values_check_in_linear_time_f64_of_a_bare_decimal() {
    one_cast_of_many_values("2.5", "f64");
}

#[test]
fn casts_of_a_call_of_many_values_check_in_linear_time_many_casts_f64_of_a_bare_decimal() {
    many_casts_of_two_values("2.5", "f64");
}

#[test]
fn casts_of_a_call_of_many_values_check_in_linear_time_scalar_of_a_bare_decimal() {
    one_cast_of_many_values("2.5", "scalar");
}

#[test]
fn casts_of_a_call_of_many_values_check_in_linear_time_many_casts_scalar_of_a_bare_decimal() {
    many_casts_of_two_values("2.5", "scalar");
}
