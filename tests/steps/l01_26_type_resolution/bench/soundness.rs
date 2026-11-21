use zed_tests::scaling;

use super::super::scaling::resolved;
use super::super::soundness::{
    component_exponents, else_nested_deep, else_of_many_nested_fields, nested_component_exponent,
    uses_left_on_classes,
};

/// CHK-obligation-sweep: the end of the walk reads each class and the uses left on it once,
/// each looked up in the set of uses met by their mask in O(1): `n` such classes and `n`
/// generic functions check in time linear in `n`.
#[test]
fn the_end_of_walk_check_scales() {
    let units = resolved(400, uses_left_on_classes);
    scaling::check(
        "the end-of-walk check over n classes with uses left",
        400,
        |n| {
            assert_eq!(units[&n].check().errors.len(), 0);
        },
    );
}

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

/// ELSE-explicit-atoms x2: what an `else` pattern of `n` fields takes is found by one visit of
/// each field of each payload shape the type lists, so `n` nested fields check in time linear
/// in `n`.
#[test]
fn an_else_of_many_nested_fields_scales() {
    let units = resolved(400, else_of_many_nested_fields);
    scaling::check("an else pattern of n nested fields", 400, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// ELSE-explicit-atoms x2: a pattern nested `d` deep is read on an explicit stack, one frame a
/// level, so it checks in time linear in `d` and needs no call stack as deep.
#[test]
fn an_else_nested_deep_scales() {
    let units = resolved(200, else_nested_deep);
    scaling::check("an else pattern nested d deep", 200, |d| {
        let info = units[&d].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}
