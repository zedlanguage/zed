//! Printing a diagnostic that quotes a string of n bytes is linear in n: the benchmark of this
//! step, run by `tools/run_tests.sh --bench` and left out of its default run
//! (TEST-bench-move-rest). Its check besides the ratio is made at small sizes by
//! `a_quoted_string_of_a_few_escapes_prints_escaped`.

use zed_tests::scaling;

use crate::type_names::lambdas_at_one_type_variable;
use crate::{prints_no_esc, quoted};

/// Row FAIL-typevar-free-in-checker: a call that passes n lambdas, each at a parameter of type
/// `(T) -> T`, puts each off and checks it against the signature with `T` fixed once, a queue
/// of n places and one replacement of a signature of size n: O(n) with persistent bindings.
#[test]
fn a_call_of_n_lambdas_at_one_type_variable_scales() {
    let inputs = scaling::inputs(200, lambdas_at_one_type_variable);
    scaling::check(
        "a call passing n lambdas at the type variable `T`",
        200,
        |n| {
            zedc::run::load(inputs[&n].as_bytes()).expect("accepted");
        },
    );
}

#[test]
fn printing_a_quoted_string_scales() {
    let inputs = scaling::inputs(4000, quoted);
    scaling::check_order("a diagnostic quoting a string of n bytes", 4000, 1, |n| {
        let (d, t) = &inputs[&n];
        prints_no_esc(d, t);
    });
}
