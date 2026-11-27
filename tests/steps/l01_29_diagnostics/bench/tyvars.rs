//! Printing signatures of `n` type variables, at `n` and `8n` (`tyvars.rs`). The signatures
//! are built before the timing.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::sig_of as sig;

use crate::tyvars::{
    a_signature_of_many_variables_printed, chain, chain_printed, each_twice, lookups,
    lookups_printed, many, nested, nested_signatures_printed,
    variables_that_each_stand_twice_named,
};

#[test]
fn printing_a_chain_of_lookups_scales() {
    // PRINT-no-underscore-rest: the d results of `p[0]...[0]` are rewritten in one walk
    // (`closed_rewrites`), each put in by reference, so the text is O(d), not the O(d^2) of
    // replacing the signature once per level; the time is the whole rejection.
    let n = 200;
    let srcs = scaling::inputs(n, chain);
    scaling::check("printing a chain of n lookups as one map", n, |size| {
        chain_printed(&srcs[&size], size);
    });
}

#[test]
fn printing_a_parameter_of_many_lookups_scales() {
    // PRINT-hidden-var: the n lookups of one parameter become n arrows, each found once
    // (`Sig::uses_written`); the time is the whole rejection, checking included.
    let n = 200;
    let srcs = scaling::inputs(n, lookups);
    scaling::check("printing a parameter of n lookups as a map", n, |size| {
        lookups_printed(&srcs[&size], size);
    });
}

#[test]
fn printing_signatures_of_many_variables_scales() {
    // Each signature is built only in the process that prints it (`scaling::check_inputs`;
    // FAIL-bench-first-phase-past-20s-l0126-l0129).
    let n = 7200;
    let wide = |m: usize| (m, sig(&many(m), "f"));
    scaling::check_inputs(
        "printing a signature of n type variables",
        n,
        wide,
        |(size, s)| {
            a_signature_of_many_variables_printed(s, *size);
        },
    );
    let deep = |m: usize| (m, nested(m));
    scaling::check_inputs(
        "printing n nested signatures that bound one name",
        n,
        deep,
        |(size, t)| nested_signatures_printed(t, *size),
    );
}

#[test]
fn naming_many_variables_that_each_stand_twice_scales() {
    // Counting the places of each variable, then naming each in one pass with a hash lookup
    // per mark, is linear in the text here: these types hold no union (COMPLEXITY.md F169).
    // Each signature is built only in the process that names it (`scaling::check_inputs`;
    // FAIL-bench-first-phase-past-20s-l0126-l0129).
    let n = 15_000;
    let built = |m: usize| (m, sig(&each_twice(m), "f"));
    scaling::check_inputs(
        "naming n variables that each stand twice",
        n,
        built,
        |(size, s)| {
            variables_that_each_stand_twice_named(s, *size);
        },
    );
}
