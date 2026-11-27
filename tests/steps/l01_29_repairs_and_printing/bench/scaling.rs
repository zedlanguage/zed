//! The checks of `scaling.rs` at `n` and `8n`, held to the limit of a pass of order n
//! (TEST-bench-move-l0125). Each input is built at both sizes before any run is timed.

use zed_tests::scaling;
use zedc::check::derivation_steps;

use crate::scaling::*;

#[test]
fn placing_a_diagnostic_on_every_line_scales() {
    let n = 13_000;
    let srcs = scaling::inputs(n, unresolved);
    scaling::check("placing a diagnostic on each of n lines", n, |k| {
        a_diagnostic_on_every_line(&srcs[&k], k);
    });
}

/// The whole check of [`doubled`], parse to message. The derivation is a small part of it
/// (468,262 of 1,382,527,695 instructions at 2100 bindings, TEST-l01_29-share), so this holds
/// the chain; [`deriving_through_values_read_twice_scales`] holds the derivation.
#[test]
fn checking_a_chain_read_twice_scales() {
    let n = 2100;
    let srcs = scaling::inputs(n, doubled);
    scaling::check(
        "the check of a chain read twice at each of n bindings",
        n,
        |k| derived_through_values_read_twice(&srcs[&k], k),
    );
}

/// The steps of the derivations of a rejection ([`derivation_steps`]: each step
/// `Ck::derivation_lines` takes, and each part the derivation builds), at `n` and `8n`, held
/// to [`scaling::PREFERRED`] by [`scaling::hold_linear`]: where `doubled` reads each binding
/// twice and `unions_inside` meets `a_(i-1)` through two tuples, a walk that went again
/// through the steps it shares would count Theta(n^2) steps (DERIV-too-large-chain-quadratic,
/// SCALE-derivation-lines-memo). A count is not timed, so it holds the derivation alone,
/// which a timing of the whole check does not: there the derivation is 0.034% of the work,
/// and a quadratic of fewer than 29 instructions a pair passes. Controls (TEST-l01_29-share):
/// one more step for each 4096 steps already keyed, at each step `derivation_lines` enters,
/// measured 24,042 and 280,108 steps, 11.65 times, and failed; one for each 65,536 passed.
/// The cost of one union of two sets of lines is not a step;
/// [`checking_a_chain_read_twice_scales`] times it with the rest.
#[test]
fn deriving_through_values_read_twice_scales() {
    for (what, n, make) in [
        (
            "the derivation of a chain read twice at each of n bindings",
            2100,
            doubled as fn(usize) -> String,
        ),
        (
            "the derivation of a chain of n tuples meeting a name twice",
            1000,
            crate::type_size::unions_inside,
        ),
    ] {
        let srcs = scaling::inputs(n, make);
        let steps = |k: usize| {
            derivation_steps();
            crate::rejected(&srcs[&k]);
            let steps = derivation_steps();
            // The walk takes each binding: a count that stays the same as `k` grows, as
            // `derivation_steps` gave before it counted `derivation_lines`, holds nothing.
            assert!(steps >= k as u64, "{what}: {steps} steps at {k}");
            steps
        };
        let small = steps(n);
        let large = steps(scaling::FACTOR * n);
        scaling::hold_linear(what, "derivation steps", small, large);
    }
}

#[test]
fn the_reasons_of_a_class_narrowed_many_times_scale() {
    let n = 1000;
    scaling::on_a_stack(1 << 29, || {
        let srcs = scaling::inputs(n, summed_condition);
        scaling::check("the reasons of a class merged n times", n, |k| {
            the_reasons_of_a_class_merged(&srcs[&k], k);
        });
    });
}

#[test]
fn a_message_with_many_definitions_scales() {
    let n = 2600;
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
    let n = 5700;
    let srcs = scaling::inputs(n, zero_chain);
    scaling::check(
        "the message of a division by the last of a chain of n names from -0r",
        n,
        |k| a_chain_of_names_to_a_negated_zero(&srcs[&k], k),
    );
}

#[test]
fn a_repair_tried_over_a_chain_of_names_scales() {
    let n = 5700;
    let srcs = scaling::inputs(n, zero_chain_tried);
    scaling::check(
        "the message of a `+` with a tried repair, read through a chain of n names from -0r",
        n,
        |k| a_repair_tried_over_a_chain_of_names(&srcs[&k], k),
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
    let n = 2800;
    let srcs = scaling::inputs(n, tuple_compared);
    scaling::check("checking the n components offered for an n-tuple", n, |k| {
        the_components_offered_for_a_tuple(&srcs[&k], k)
    });
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
    let n = 200;
    let srcs = scaling::inputs(n, carried_fixes);
    scaling::check(
        "checking the carried fixes of a call of n arguments",
        n,
        |k| the_carried_fixes_of_the_arguments(&srcs[&k], k),
    );
}

#[test]
fn the_fixes_of_many_arguments_not_checked_apart_scale() {
    let n = 200;
    let srcs = scaling::inputs(n, carried_fixes_not_apart);
    scaling::check(
        "checking the fixes of a call of n arguments at parameters not checked apart",
        n,
        |k| the_fixes_of_arguments_not_apart(&srcs[&k], k),
    );
}

#[test]
fn many_unfixed_decimal_arguments_scale() {
    let n = 3900;
    let srcs = scaling::inputs(n, unfixed_decimal_arguments);
    scaling::check(
        "checking a call of n decimal literals at n parameters with no type",
        n,
        |k| unfixed_decimal_arguments_checked(&srcs[&k]),
    );
}

#[test]
fn many_decimal_arguments_past_f64_scale() {
    let n = 3900;
    let srcs = scaling::inputs(n, past_f64_arguments);
    scaling::check(
        "rejecting a call of n decimal literals past f64 at n parameters with no type",
        n,
        |k| past_f64_arguments_rejected(&srcs[&k], k),
    );
}

/// The fixes carried into the n arguments, each of a parameter that is a type variable of
/// its own, checked in rounds (MSG-many-args-generic). Negative control, run once and not
/// committed: with them checked one by one, each by a trial of the whole call (`params_apart`
/// in place of `params_own_apart`), this ran out of time (72 s).
#[test]
fn many_division_arguments_scale() {
    let n = 400;
    let srcs = scaling::inputs(n, division_arguments);
    scaling::check(
        "rejecting a call of n divisions of literals at n parameters with no type",
        n,
        |k| division_arguments_rejected(&srcs[&k], k),
    );
}

/// The `rat` of the cast's fix lent to the division beside it among n arguments, one more
/// check of the call and one pass over the arguments (TEST-params-own-apart-red). Negative
/// control, run once and not committed: with the type lent to each other argument by a check
/// of the call of its own, this ran out of time (232 s; 0.84 s with the change).
#[test]
fn a_cast_beside_a_division_of_one_variable_among_many_arguments_scales() {
    let n = 1000;
    let srcs = scaling::inputs(n, cast_beside_a_division);
    scaling::check(
        "offering each carrier for a cast beside a division among n arguments",
        n,
        |k| cast_beside_a_division_offered(&srcs[&k], k),
    );
}

#[test]
fn the_merges_between_a_value_and_its_use_scale() {
    let n = 4000;
    let srcs = scaling::inputs(n, defaults_chain);
    scaling::check(
        "the merges between a value and its use, 2n defaults",
        n,
        |k| the_merges_between_a_value_and_its_use(&srcs[&k], k),
    );
}

#[test]
fn the_headline_repair_of_a_long_call_scales() {
    let n = 260_000;
    let srcs = scaling::inputs(n, one_repair_in_a_long_call);
    scaling::check("the headline repair of a call n bytes long", n, |k| {
        the_headline_repair_of_a_call(&srcs[&k], k);
    });
}

/// Negative controls, run once and not committed (MSG-many-args-steps-square): with the
/// repairs of the arguments the call takes tried again, or with the derivation of the call's
/// error walked anew for each argument, this failed at 13.7 times the work for 8 times n.
#[test]
fn a_long_call_taking_all_but_one_argument_scales() {
    let n = 200;
    for sep in [", ", ",\n  "] {
        let srcs = scaling::inputs(n, |k| taken_beside_one_refused(k, sep));
        scaling::check(
            "the repairs of a call that takes n arguments and refuses one",
            n,
            |k| only_the_refused_argument_repaired(&srcs[&k]),
        );
    }
}

#[test]
fn a_text_repair_of_many_shapes_scales() {
    let n = 19_000;
    let srcs = scaling::inputs(n, a_call_of_many_tuple_lengths);
    scaling::check("the text repair of a union of n tuple components", n, |k| {
        a_text_repair_of_shapes(&srcs[&k])
    });
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
    scaling::check("the literal a cast gives on a text of d digits", d, |k| {
        the_literal_of_a_long_text(&srcs[&k], k)
    });
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
    let n = 640;
    let srcs = scaling::inputs(n, fractions_compared);
    scaling::check(
        "n comparisons with fraction texts, each repaired by the cast kept around the text",
        n,
        |k| the_cast_of_a_literal_offered_in_comparisons(&srcs[&k], k),
    );
}

#[test]
fn offering_the_literal_of_a_cast_of_a_literal_in_comparisons_scales() {
    let n = 500;
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
fn naming_each_call_of_a_chain_scales() {
    let n = 1000;
    let srcs = scaling::inputs(n, call_chain);
    scaling::check(
        "the rejection at a call naming each of a chain of n calls",
        n,
        |k| each_call_of_the_chain_named(&srcs[&k], k),
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
