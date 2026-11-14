use zed_tests::scaling;

use super::super::atom_scaling::{
    chain_of_atom_tests, chain_of_computed_names, chain_of_elses, chain_of_equalities,
    chain_of_handlers, chain_of_handlers_calling, chain_of_names, chain_of_own_atoms,
    handled_calls, keys_handled, method_chain, nested_handlers, one_call_of_many_arguments,
    passing_calls, tests_of_atoms,
};
use super::super::info;
use super::super::scaling::resolved;

#[test]
fn a_parameter_tested_against_many_atoms_scales() {
    // Each test adds its atom to the parameter's set, the small set into the large one.
    let units = resolved(12_800, tests_of_atoms);
    scaling::check("a parameter tested against n atoms", 12_800, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

#[test]
fn a_parameter_bound_to_a_chain_of_names_scales() {
    // The union-find joins each name to the chain's class in near-constant time, and each test
    // then adds its atom to the class's set.
    let units = resolved(8000, chain_of_names);
    scaling::check("a parameter bound to a chain of n names", 8000, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

#[test]
fn a_chain_of_atoms_from_elsewhere_than_the_parameter_scales() {
    // Each name passes on the atoms of the one before it from elsewhere than `line`, and adds
    // its own, the small set into the large one.
    let units = resolved(1000, chain_of_own_atoms);
    scaling::check("a chain of n names each adding an atom", 1000, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
        assert_eq!(info.sigs.values().next().unwrap().arrows.len(), 2);
    });
}

#[test]
fn a_chain_of_functions_passing_a_handled_parameter_on_scales() {
    let units = resolved(1600, chain_of_handlers);
    scaling::check(
        "a chain of n functions passing a handled parameter on",
        1600,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

#[test]
fn a_chain_of_functions_passing_a_handled_parameter_on_as_a_receiver_scales() {
    let method = |i: usize| format!("x.h{}()", i - 1);
    let units = resolved(1000, |n| chain_of_handlers_calling(n, method));
    scaling::check(
        "a chain of n functions passing a handled parameter on as a receiver",
        1000,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

/// One function calling `r` n times on its handled parameter as `call` writes the call (see
/// [`handled_calls`]).
fn handled_calls_scale(call: &str) {
    let units = resolved(1600, |n| handled_calls(n, call));
    scaling::check(
        &format!("one function calling `{call}` n times"),
        1600,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

#[test]
fn many_calls_passing_a_handled_parameter_on_scale_as_arguments() {
    handled_calls_scale("r(x)");
}

#[test]
fn many_calls_passing_a_handled_parameter_on_scale_as_receivers() {
    handled_calls_scale("x.r()");
}

#[test]
fn many_calls_passing_a_handled_parameter_on_scale_as_receivers_without_parentheses() {
    handled_calls_scale("x.r");
}

#[test]
fn many_calls_passing_a_handled_parameter_on_scale_through_a_higher_order_function() {
    handled_calls_scale("ap(r, x)");
}

#[test]
fn many_calls_passing_a_handled_parameter_on_scale_through_a_computed_callee() {
    handled_calls_scale("(if true { r } else { r })(x)");
}

#[test]
fn many_calls_passing_a_handled_parameter_on_scale_to_a_lambda() {
    handled_calls_scale("ap((positional y) -> trim(y), x)");
}

#[test]
fn a_chain_of_method_calls_without_parentheses_scales() {
    // `x.r.r` … `.r`, n deep: each call is applied once more on the atoms from outside, and
    // that application takes its receiver's type as found, so the chain is checked in time
    // linear in n.
    scaling::check("a chain of n method calls without parentheses", 5000, |n| {
        let (info, _) = info(&method_chain(n));
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

#[test]
fn a_chain_of_functions_each_testing_an_atom_of_its_own_scales() {
    // Each pass-by costs a set difference per arrow.
    let units = resolved(2000, chain_of_atom_tests);
    scaling::check(
        "a chain of n functions each testing an atom of its own",
        2000,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

/// One function calling `call` n times on a value that may be a string, `#a` or `#b` (see
/// [`passing_calls`]).
///
/// The sizes are those at which a cost per call in the number of calls fails: each call
/// `h(v)` checks in about 500,000 instructions, so at 200 and 1,600 calls a copy of
/// `Info::passes` at each pass-by (`Ck::pass_at`) still passed (`h(v)`: 18.6 times the
/// instructions, 15.3 times the bytes); at 1,000 and 8,000 the same copy takes 38.4 and
/// 32.4 times, and the code without it 8.0 and 8.0 (ISSUE1-passby-scale).
fn passing_calls_scale(call: &str) {
    let units = resolved(1000, |n| passing_calls(n, call));
    scaling::check(
        &format!("one function calling `{call}` n times"),
        1000,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
            assert_eq!(info.passes.len(), n, "{call}");
        },
    );
}

#[test]
fn many_calls_passing_some_atoms_of_their_argument_by_scale_to_a_function() {
    passing_calls_scale("h(v)");
}

#[test]
fn many_calls_passing_some_atoms_of_their_argument_by_scale_to_a_lambda() {
    passing_calls_scale("ap((positional y) -> trim(y), v)");
}

#[test]
fn one_call_passing_the_atoms_of_many_arguments_by_scales() {
    // `Ck::pass_at` copied the call's list of entries for each such argument and searched it,
    // so one call of n arguments cost n^2 (PASS-at-args); the entries are now a map by argument
    // span.
    let units = resolved(10_000, |n| one_call_of_many_arguments(n, |_| "v"));
    scaling::check(
        "one call of n arguments that each pass atoms by",
        10_000,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
            assert_eq!(info.passes.len(), 1);
            assert_eq!(info.passes.values().map(|at| at.len()).sum::<usize>(), n);
        },
    );
}

#[test]
fn a_parameter_trimmed_through_a_chain_of_names_scales() {
    // Each name's set is the next one's with one atom added, in the order Tarjan's walk
    // finishes them.
    let units = resolved(4000, chain_of_computed_names);
    scaling::check(
        "a parameter trimmed through a chain of n names",
        4000,
        |n| {
            let info = units[&n].check();
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

#[test]
fn a_parameter_inside_many_nested_handlers_scales() {
    let units = resolved(6400, nested_handlers);
    scaling::check("a parameter inside n nested handlers", 6400, |n| {
        let info = units[&n].check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

/// Each `else` and each failed `==` on a class that may still take other values leaves a
/// class of its own, joined with the class it tests where either takes a carrier: two passes
/// over the links, so a chain of `n` is joined in time linear in `n`.
fn chain_of_tests_scales(what: &str, text: fn(usize) -> String, n: usize) {
    let units = resolved(n, text);
    scaling::check(what, n, |m| {
        let info = units[&m].check();
        assert!(info.errors.is_empty(), "{what}: {:?}", info.errors);
    });
}

#[test]
fn chains_of_tests_that_leave_values_of_their_own_scale_elses() {
    chain_of_tests_scales("a chain of n elses", chain_of_elses, 6000);
}

#[test]
fn chains_of_tests_that_leave_values_of_their_own_scale_equalities() {
    chain_of_tests_scales("a chain of n equalities", chain_of_equalities, 1200);
}

#[test]
fn chains_of_tests_that_leave_values_of_their_own_scale_handled_keys() {
    // The key of `args[k]` is followed as an argument is.
    chain_of_tests_scales("n functions handling their key", keys_handled, 1000);
}
