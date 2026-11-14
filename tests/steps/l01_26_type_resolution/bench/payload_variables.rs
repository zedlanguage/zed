use zed_tests::scaling;

use super::super::Resolved;
use super::super::payload_variables::{in_atoms_in_a_tuple, in_atoms_twice_in_a_tuple};

/// Besides its ratio: the equality is refused. Small instance:
/// `payload_variables::a_function_deep_in_a_payload_in_a_tuple_is_refused_by_equality`.
#[test]
fn a_variable_deep_in_a_payload_in_a_tuple_is_checked_in_linear_time() {
    // Each row and payload shape keeps whether it holds a variable at any depth, so the need
    // `==` puts on the tuple, the replacement of the parameter's variable at the call, and the
    // settling of the signature each enter a shared row or shape once: `O(n)` for `n` atoms,
    // and for the payload held twice too, whose tree has `2^n` leaves.
    type Family = fn(usize, &str) -> String;
    for (what, text, arg, errors) in [
        (
            "a function n atoms deep in a tuple",
            in_atoms_in_a_tuple as Family,
            "scale",
            1,
        ),
        (
            "an integer n atoms deep in a tuple",
            in_atoms_in_a_tuple,
            "2",
            0,
        ),
        (
            "a function put twice in an atom by n bindings, in a tuple",
            in_atoms_twice_in_a_tuple,
            "scale",
            1,
        ),
        (
            "an integer put twice in an atom by n bindings, in a tuple",
            in_atoms_twice_in_a_tuple,
            "2",
            0,
        ),
    ] {
        let units = scaling::inputs(500, |n| Resolved::new(&text(n, arg)));
        scaling::check_order(what, 500, 1, |n| {
            let info = units[&n].check();
            assert_eq!(info.errors.len(), errors, "{what} at {n}");
        });
    }
}
