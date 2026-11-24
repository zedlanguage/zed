//! Remaps and `group` calls whose source's entries have a type not known where the call is
//! checked: a class of a generic function's parameter, or the unknown (plan rows GROUP-nested,
//! REMAP-dynamic-deep-binder). Each such entry may be a family at run time, so the value binder,
//! or `group`'s function, takes it whole: the `reindex`, which walks to the leaves, takes the
//! source with each entry held in a tuple of one (`RemapPlan::boxed`, `Info::boxed_groups`).

use zed_tests::step_helpers::l01_16_elaboration::value;

/// A generic function's `group` given a list of lists keeps each row whole, the empty one
/// included: with the walk to the leaves, the function took a leaf and the empty row was lost.
/// Before GROUP-nested the checker refused the call as a later step.
#[test]
fn a_generic_group_keeps_each_row_whole() {
    let src = "g(positional m) = m.group(r -> r.count);\nx = g([[1, 2], [], [3]]);\n";
    assert_eq!(
        value(src, "x"),
        "{0 -> {1 -> {}}, 1 -> {2 -> {0 -> 3}}, 2 -> {0 -> {0 -> 1, 1 -> 2}}}"
    );
    let src = "g(positional m) = m.group(r -> r >< (+));\nx = g({ \"a\" -> { 1 -> 10 } });\n";
    assert_eq!(value(src, "x"), "{10 -> {\"a\" -> {1 -> 10}}}");
}

/// A generic function's remap binds each row whole whatever the depth of the value at each call,
/// called at a shallow value first and at a deeper one after, and the reverse.
#[test]
fn a_generic_remap_binds_the_row_at_every_depth_of_call() {
    let f = "g(positional m) = m as (k -> r) into (k -> r);\n";
    for calls in [
        "x = g({ 0 -> { 1 -> 2 } });\n",
        "a = g({ 0 -> 5 });\nx = g({ 0 -> { 1 -> 2 } });\n",
        "x = g({ 0 -> { 1 -> 2 } });\na = g({ 0 -> 5 });\n",
    ] {
        assert_eq!(
            value(&format!("{f}{calls}"), "x"),
            "{0 -> {1 -> 2}}",
            "{calls}"
        );
    }
    let src = format!("{f}x = [{{ 0 -> 5 }}, {{ 0 -> {{ 1 -> 2 }} }}].map(g);\n");
    assert_eq!(value(&src, "x"), "{0 -> {0 -> 5}, 1 -> {0 -> {1 -> 2}}}");
    let src = "ap(positional g, positional y) = g(y);\n\
               x = ap(m -> m as (k -> r) into (k -> r), { 0 -> { 1 -> { 2 -> 3 } } });\n";
    assert_eq!(value(src, "x"), "{0 -> {1 -> {2 -> 3}}}");
}
