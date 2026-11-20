//! Scaling of the checker on atoms a body makes and a call gives (CHK-index-else-bubble):
//! the table of where each expression's atoms go is built once a unit, in one pass, and each
//! call composes the fates along its need's sites.

use zed_tests::scaling;

use super::super::bubble::{body_of_bindings, chain_of_helpers, helpers_giving_their_atom};
use super::super::scaling::resolved;

#[test]
fn many_calls_giving_a_body_s_atom_scale() {
    let units = resolved(200, helpers_giving_their_atom);
    scaling::check("n calls each giving its body's atom", 200, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

#[test]
fn a_chain_of_calls_passing_a_body_s_atom_on_scale() {
    let units = resolved(100, chain_of_helpers);
    scaling::check("a chain of n calls passing a body's atom on", 100, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

#[test]
fn a_body_of_many_bindings_scale() {
    let units = resolved(500, body_of_bindings);
    scaling::check("a body passing its atom through n bindings", 500, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}
