//! The checks of `scaling.rs` at `n` and `8n`, held to the limit of a pass of order n
//! (TEST-bench-move-l0125). Each input is built at both sizes before any run is timed.

use zed_tests::scaling;

use crate::scaling::*;

#[test]
fn placing_a_diagnostic_on_every_line_scales() {
    let n = 500;
    let srcs = scaling::inputs(n, unresolved);
    scaling::check("placing a diagnostic on each of n lines", n, |k| {
        a_diagnostic_on_every_line(&srcs[&k], k);
    });
}

#[test]
fn deriving_through_values_read_twice_scales() {
    let n = 400;
    let srcs = scaling::inputs(n, doubled);
    scaling::check(
        "the derivation of a chain read twice at each of n bindings",
        n,
        |k| derived_through_values_read_twice(&srcs[&k]),
    );
}

#[test]
fn the_reasons_of_a_class_narrowed_many_times_scale() {
    let n = 1000;
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(move || {
            let srcs = scaling::inputs(n, summed_condition);
            scaling::check("the reasons of a class merged n times", n, |k| {
                the_reasons_of_a_class_merged(&srcs[&k], k);
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn a_message_with_many_definitions_scales() {
    let n = 200;
    let srcs = scaling::inputs(n, shared_parts);
    scaling::check("a message with n parts written more than once", n, |k| {
        a_message_with_definitions(&srcs[&k], k);
    });
}

#[test]
fn deriving_reads_of_many_divisions_of_literals_scales() {
    let n = 200;
    let srcs = scaling::inputs(n, read_divisions);
    scaling::check_order(
        "the derivations of n reads of names defined as divisions of literals",
        n,
        1,
        |k| derived_reads_of_divisions_of_literals(&srcs[&k], k),
    );
}

#[test]
fn a_chain_of_names_to_a_negated_zero_prints_in_linear_time() {
    let n = 1000;
    let srcs = scaling::inputs(n, zero_chain);
    scaling::check(
        "the message of a division by the last of a chain of n names from -0r",
        n,
        |k| a_chain_of_names_to_a_negated_zero(&srcs[&k], k),
    );
}

#[test]
fn checking_each_offered_fix_as_written_scales() {
    let n = 200;
    let srcs = scaling::inputs(n, checked_fixes);
    scaling::check("checking the fixes of 3n rejections as written", n, |k| {
        each_offered_fix_checked_as_written(&srcs[&k], k);
    });
}

#[test]
fn checking_the_components_offered_for_a_wide_tuple_scales() {
    let n = 200;
    let srcs = scaling::inputs(n, tuple_compared);
    scaling::check(
        "checking the n components offered for an n-tuple",
        n,
        |k| the_components_offered_for_a_tuple(&srcs[&k], k),
    );
}

/// The message of a call of `n` literals at `n` parameters of carrier `c`.
fn many_literal_arguments_scale(c: &str, fixed: Option<&str>) {
    let n = 200;
    let srcs = scaling::inputs(n, |k| many_literal_arguments(k, c));
    scaling::check(
        &format!("the message of a call of n literals at n {c} parameters"),
        n,
        |k| literal_arguments_refused(&srcs[&k], k, c, fixed),
    );
}

#[test]
fn many_literal_arguments_refused_at_their_parameters_scale() {
    many_literal_arguments_scale("rat", Some("1.0"));
}

#[test]
fn many_literal_arguments_refused_at_int_parameters_scale() {
    many_literal_arguments_scale("int", None);
}

#[test]
fn the_carried_fixes_of_many_arguments_scale() {
    let n = 100;
    let srcs = scaling::inputs(n, carried_fixes);
    scaling::check(
        "checking the carried fixes of a call of n arguments",
        n,
        |k| the_carried_fixes_of_the_arguments(&srcs[&k], k),
    );
}

#[test]
fn many_unfixed_decimal_arguments_scale() {
    let n = 200;
    let srcs = scaling::inputs(n, unfixed_decimal_arguments);
    scaling::check(
        "the message of a call of n decimal literals at n parameters with no type",
        n,
        |k| unfixed_decimal_arguments_refused(&srcs[&k], k),
    );
}

#[test]
fn the_merges_between_a_value_and_its_use_scale() {
    let n = 1000;
    let srcs = scaling::inputs(n, defaults_chain);
    scaling::check(
        "the merges between a value and its use, 2n defaults",
        n,
        |k| the_merges_between_a_value_and_its_use(&srcs[&k], k),
    );
}

#[test]
fn the_headline_repair_of_a_long_call_scales() {
    let n = 4000;
    let srcs = scaling::inputs(n, one_repair_in_a_long_call);
    scaling::check("the headline repair of a call n bytes long", n, |k| {
        the_headline_repair_of_a_call(&srcs[&k], k);
    });
}

#[test]
fn a_text_repair_of_many_shapes_scales() {
    let n = 800;
    let srcs = scaling::inputs(n, a_call_of_many_tuple_lengths);
    scaling::check(
        "the text repair of a union of n tuple components",
        n,
        |k| a_text_repair_of_shapes(&srcs[&k]),
    );
}

#[test]
fn writing_the_literal_a_cast_gives_scales() {
    let n = 200;
    let srcs = scaling::inputs(n, texts_for_ints);
    scaling::check(
        "n rejections, each repaired by the literal a cast gives",
        n,
        |k| the_literal_a_cast_gives(&srcs[&k], k),
    );
}

#[test]
fn writing_the_literal_of_a_long_text_scales() {
    let d = 4000;
    let srcs = scaling::inputs(d, a_long_text_multiplied);
    scaling::check(
        "the literal a cast gives on a text of d digits",
        d,
        |k| the_literal_of_a_long_text(&srcs[&k], k),
    );
}

#[test]
fn offering_the_literal_first_in_comparisons_scales() {
    let n = 200;
    let srcs = scaling::inputs(n, texts_compared);
    scaling::check(
        "n comparisons with texts, each repaired first by the literal a cast gives",
        n,
        |k| the_literal_offered_first_in_comparisons(&srcs[&k], k),
    );
}

#[test]
fn offering_the_literal_of_a_long_text_in_a_comparison_scales() {
    let d = 4000;
    let srcs = scaling::inputs(d, a_long_text_compared);
    scaling::check(
        "the literal a cast gives on a compared text of d digits",
        d,
        |k| the_literal_of_a_long_text_in_a_comparison(&srcs[&k], k),
    );
}

#[test]
fn deciding_an_ordering_with_a_long_number_text_offers_no_text_comparison_scales() {
    let d = 2000;
    let srcs = scaling::inputs(d, an_f64_ordered_with_a_long_fraction_text);
    scaling::check(
        "an ordering of an f64 with a fraction text of d digits on each side",
        d,
        |k| an_ordering_with_a_number_text_offers_no_text_comparison(&srcs[&k]),
    );
}

#[test]
fn offering_the_cast_of_a_literal_in_comparisons_scales() {
    let n = 200;
    let srcs = scaling::inputs(n, fractions_compared);
    scaling::check(
        "n comparisons with fraction texts, each repaired by the cast kept around the text",
        n,
        |k| the_cast_of_a_literal_offered_in_comparisons(&srcs[&k], k),
    );
}

#[test]
fn offering_the_literal_of_a_cast_of_a_literal_in_comparisons_scales() {
    let n = 200;
    let srcs = scaling::inputs(n, casts_compared);
    scaling::check(
        "n comparisons with casts of texts, each repaired by a literal or answered",
        n,
        |k| the_literal_of_a_cast_of_a_literal_offered(&srcs[&k], k),
    );
}

#[test]
fn offering_the_literal_of_a_long_cast_of_a_text_in_a_comparison_scales() {
    let d = 4000;
    let srcs = scaling::inputs(d, a_long_cast_of_a_text_compared);
    scaling::check(
        "the literal of a compared cast of a text of d digits",
        d,
        |k| the_literal_of_a_long_cast_of_a_text(&srcs[&k], k),
    );
}

#[test]
fn offering_the_cast_of_a_long_fraction_text_in_a_comparison_scales() {
    let d = 4000;
    let srcs = scaling::inputs(d, a_long_fraction_text_compared);
    scaling::check(
        "the cast kept around a compared fraction text of d digits",
        d,
        |k| the_cast_of_a_long_fraction_text(&srcs[&k], k),
    );
}

#[test]
fn repairing_an_ordering_of_an_int_with_a_long_fraction_text_scales() {
    let d = 2000;
    let srcs = scaling::inputs(d, an_int_ordered_with_a_long_fraction_text);
    scaling::check(
        "an ordering of an int with a fraction text of d digits",
        d,
        |k| an_ordering_of_an_int_with_a_fraction_text_repaired(&srcs[&k], k),
    );
}

#[test]
fn repairing_orderings_of_ints_with_fraction_texts_scales() {
    let n = 200;
    let srcs = scaling::inputs(n, int_orderings_with_fractions);
    scaling::check(
        "n orderings of an int with a fraction text, each repaired by casting both operands",
        n,
        |k| orderings_of_ints_with_fraction_texts_repaired(&srcs[&k], k),
    );
}
