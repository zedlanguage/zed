use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

use super::super::param_follows::comparisons;

#[test]
fn comparisons_with_a_parameter_are_checked_in_linear_time() {
    zed_tests::deep::on_small_stack(|| {
        let n = 5000;
        let srcs = [comparisons(n), comparisons(scaling::FACTOR * n)];
        scaling::check(
            "checking a body of n comparisons of a parameter with operations on literals",
            n,
            |m| {
                type_errors(&srcs[usize::from(m != n)]);
            },
        );
    });
}
