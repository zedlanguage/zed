//! Scaling of the checker on atoms a body makes and a call gives (CHK-index-else-bubble):
//! the table of where each expression's atoms go is built once a unit, in one pass, and each
//! call composes the fates along its need's sites.

use zed_tests::scaling;

use super::super::bubble::{
    body_of_bindings, body_of_uncalled_inner_pushes, body_pushing_a_family,
    body_pushing_a_nested_family, body_pushing_parameters, chain_of_helpers,
    helpers_giving_their_atom, helpers_pushing_their_parameter, lambdas_of_own_type_variables,
    pushes_narrowed_by_type_variables, uncalled_inner_push_of_parameters,
};
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

/// The check of a push of an untyped parameter is one need per push, met at each call
/// (row PORT-untyped-arg): linear in the pushes and calls.
#[test]
fn many_pushes_of_untyped_parameters_scale() {
    let units = resolved(200, helpers_pushing_their_parameter);
    scaling::check("n helpers each pushing its untyped parameter", 200, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

#[test]
fn a_body_pushing_many_untyped_parameters_scales() {
    let units = resolved(200, body_pushing_parameters);
    scaling::check("a body pushing n untyped parameters", 200, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// Row PORT-untyped-arg-gaps: a push of a family of n untyped parameters waits on one class at
/// a time (`Ck::push_vars` in zedc-check), and the end of the helper meets it once for the
/// class it waits on and records one need on the rest; the call checks that need with its n
/// arguments once. Each step reads the family's n entries once: linear in n.
#[test]
fn a_body_pushing_a_family_of_many_untyped_parameters_scales() {
    let units = resolved(200, body_pushing_a_family);
    scaling::check(
        "a body pushing a family of n untyped parameters",
        200,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

/// Row PROOF-push-vars-other-var: the push of a family nested n deep reads its entries at
/// every depth (`push_entries` in zedc-check), each level's signature once by its visited
/// set, so the push costs O(n) beside the n bindings: linear in n.
#[test]
fn a_push_of_a_family_nested_n_deep_scales() {
    let units = resolved(200, body_pushing_a_nested_family);
    scaling::check("a push of a family nested n deep", 200, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// Row CHECK-uncalled-inner-push-refused: the end of `h` reads, once, which of its type
/// variables stand only in its n push needs (`Ck::unreached_in_pushes` in zedc-check), one
/// walk of the signature, then rewrites each such need once: linear in n.
#[test]
fn many_uncalled_inner_pushes_scale() {
    let units = resolved(100, body_of_uncalled_inner_pushes);
    scaling::check("a body holding n uncalled inner pushes", 100, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// Row CHECK-uncalled-inner-push-refused: one push need holding n variables no call binds is
/// rewritten with one replacement of its value, after one walk of the signature: linear in n.
#[test]
fn an_uncalled_inner_push_of_many_parameters_scales() {
    let units = resolved(100, uncalled_inner_push_of_parameters);
    scaling::check("an uncalled inner push of n parameters", 100, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// Row PROOF-push-vars-other-route: n tests `xi is Ti`, each against its own type variable,
/// make n classes, one lookup in the open scopes each, and n pushes each waiting on one open
/// class: linear in n. The checker alone runs; elaboration refuses the tests.
#[test]
fn pushes_narrowed_by_tests_against_type_variables_scale() {
    let units = resolved(100, pushes_narrowed_by_type_variables);
    scaling::check(
        "n pushes narrowed by tests against type variables",
        100,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

#[test]
fn lambdas_of_their_own_type_variable_scale() {
    let units = resolved(100, lambdas_of_own_type_variables);
    scaling::check(
        "n lambdas whose parameters are written as their own type variable",
        100,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

#[test]
fn a_body_of_many_bindings_scale() {
    let units = resolved(500, body_of_bindings);
    scaling::check("a body passing its atom through n bindings", 500, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}
