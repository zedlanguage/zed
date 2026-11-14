use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::Resolved;

use super::super::name_fixed::{chain, decimals};

#[test]
fn bindings_of_literals_check_in_linear_time() {
    scaling::on_a_thread(1 << 28, || {
        let n = 1100;
        let units = scaling::inputs(n, |m| Resolved::new(&chain(m)));
        scaling::check("checking a chain of n bindings of literals", n, |m| {
            units[&m].check();
        });
    });
}

#[test]
fn rejected_parts_of_a_binding_check_in_linear_time() {
    // Each rejected literal finds its part of the value by a binary search of the parts, and the
    // fixes write the binding once per carrier.
    scaling::on_a_thread(1 << 28, || {
        let n = 1600;
        let units = scaling::inputs(n, |m| Resolved::new(&decimals(m)));
        scaling::check(
            "checking a binding of a tuple of n rejected parts",
            n,
            |m| {
                units[&m].check();
            },
        );
    });
}
