use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::Resolved;

use super::super::cast_int_f64::many;

#[test]
fn casts_of_many_operations_on_literals_check_in_linear_time() {
    scaling::on_a_thread(1 << 28, || {
        let n = 200;
        let units = scaling::inputs(n, |m| Resolved::new(&many(m)));
        scaling::check(
            "checking n casts `int` and `f64` of a name of n literals and of n operations on literals",
            n,
            |m| {
                units[&m].check();
            },
        );
    });
}
