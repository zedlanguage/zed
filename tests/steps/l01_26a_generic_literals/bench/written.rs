use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

use super::super::written::long;

#[test]
fn quoting_a_literal_of_n_digits_with_underscores_scales() {
    let n = 20_000;
    let srcs = scaling::inputs(n, long);
    scaling::check("quoting a literal of n digits with `_`", n, |m| {
        type_errors(&srcs[&m]);
    });
}
