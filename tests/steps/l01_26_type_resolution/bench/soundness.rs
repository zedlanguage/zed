use zed_tests::scaling;

use super::super::scaling::resolved;
use super::super::soundness::{component_exponents, nested_component_exponent};

/// CHK-pow-component-bound: the bound an exponent puts on a component of a tuple parameter is
/// recorded once, on a path of steps from the parameter, and each call checks its argument's
/// part at that path once: `n` such functions and `2n` calls check in time linear in `n`.
#[test]
fn component_exponent_bounds_check_in_linear_time() {
    let units = resolved(200, component_exponents);
    scaling::check("checking n component exponent bounds", 200, |n| {
        assert_eq!(units[&n].check().errors.len(), n);
    });
}

/// The path of a component `d` tuples deep is `d` steps, read once where the `^` is and once
/// at each call: linear in `d`.
#[test]
fn a_component_exponent_bound_d_deep_checks_in_linear_time() {
    let units = resolved(200, nested_component_exponent);
    scaling::check("checking a component exponent bound d deep", 200, |d| {
        assert_eq!(units[&d].check().errors.len(), 1);
    });
}
