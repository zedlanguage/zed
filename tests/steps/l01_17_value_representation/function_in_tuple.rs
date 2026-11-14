//! FAIL-values-function-in-tuple, found by TEST-complete-values (author P189). Drop this file
//! into tests/steps/l01_17_value_representation/ as a module (`mod function_in_tuple;` in its
//! mod.rs) once a tuple may hold a function (row FIX-functions-in-tuples, QUESTIONS A43).

use zed_tests::step_helpers::l01_16_elaboration::elab;

/// DESIGN.md L1.17: "A tuple, an array or a struct may hold a function at any depth, as
/// `(f, 1)` ... building one is no error, and only a use that needs data is."
#[test]
fn building_a_tuple_that_holds_a_function_is_no_error() {
    let f = "f(positional v: int) = v;\n";
    for e in ["(f, 1)", "(1, (2, f))", "(#box(f), 1)"] {
        let src = format!("{f}x = {e};\n");
        assert!(elab(&src).is_ok(), "{src}: {:?}", elab(&src).err());
    }
}
