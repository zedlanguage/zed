//! Printing signatures of `n` type variables, at `n` and `8n` (`tyvars.rs`). The signatures
//! are built before the timing.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::sig_of as sig;

use crate::tyvars::{
    a_signature_of_many_variables_printed, each_twice, many, nested, nested_signatures_printed,
    variables_that_each_stand_twice_named,
};

#[test]
fn printing_signatures_of_many_variables_scales() {
    let n = 300;
    let wide = scaling::inputs(n, |m| sig(&many(m), "f"));
    scaling::check("printing a signature of n type variables", n, |size| {
        a_signature_of_many_variables_printed(&wide[&size], size);
    });
    let deep = scaling::inputs(n, nested);
    scaling::check(
        "printing n nested signatures that bound one name",
        n,
        |size| nested_signatures_printed(&deep[&size], size),
    );
}

#[test]
fn naming_many_variables_that_each_stand_twice_scales() {
    // Counting the places of each variable, then naming each in one pass with a hash lookup
    // per mark, is linear in the text here: these types hold no union (COMPLEXITY.md F169).
    let n = 1000;
    let built = scaling::inputs(n, |m| sig(&each_twice(m), "f"));
    scaling::check("naming n variables that each stand twice", n, |size| {
        variables_that_each_stand_twice_named(&built[&size], size);
    });
}
