//! A function held n deep or n times and compared with `==`, at `n` and `8n`
//! (`shared_print.rs`, row MSG-shared-print): the check and the text of the rejection.

use zed_tests::scaling;

use crate::shared_print::{SHAPES, rejected_with};

#[test]
fn a_function_held_n_deep_or_n_times_is_rejected_in_linear_time() {
    let n = 50;
    for (name, f) in SHAPES {
        let srcs = scaling::inputs(n, f);
        scaling::check(
            &format!("a function held n deep or n times, compared with ==: {name}"),
            n,
            |k| {
                rejected_with(&srcs[&k], if name == "many" { k } else { 1 });
            },
        );
    }
}
