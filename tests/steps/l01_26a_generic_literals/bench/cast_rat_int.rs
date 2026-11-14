use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::Resolved;

use super::super::cast_rat_int::many;

/// Besides its ratio: the check ends. Small instance, with no atom in the signature:
/// `cast_rat_int::casts_of_a_name_of_literals_keep_no_atom`.
#[test]
fn casts_of_a_name_of_many_literals_check_in_linear_time() {
    // Each cast reads the class's flags and restricts its mask once: no walk of its literals.
    scaling::on_a_thread(1 << 28, || {
        let n = 1200;
        let units = scaling::inputs(n, |m| Resolved::new(&many(m)));
        scaling::check(
            "checking n casts `rat(b)` of a name of n literals",
            n,
            |m| {
                units[&m].check();
            },
        );
    });
}
