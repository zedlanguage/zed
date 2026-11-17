use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

use super::super::call_arguments::int_param_divisions;

/// `n` calls `f(x: 1 / 2)` at an `int` parameter, at the top level and in `n` bodies: each is
/// one message (`Ck::int_param_division`), which walks its argument once (`open_lits`) and
/// gives it `rat` once (`Ck::lit_takes` at the top level, one `restrict` of its class in a
/// body), O(size of the argument) per call, O(n) in all.
///
/// Besides its ratio: `n` messages. Small instance:
/// `call_arguments::many_divisions_at_an_int_parameter_are_rejected_once_each`.
#[test]
fn divisions_at_an_int_parameter_scale() {
    scaling::on_a_thread(1 << 29, || {
        let n = 500;
        for body in [false, true] {
            let srcs = [
                int_param_divisions(n, body),
                int_param_divisions(scaling::FACTOR * n, body),
            ];
            assert_eq!(type_errors(&srcs[0]).len(), n);
            let what = format!("rejecting n divisions at an int parameter, in bodies: {body}");
            scaling::check(&what, n, |m| {
                type_errors(&srcs[usize::from(m != n)]);
            });
        }
    });
}
