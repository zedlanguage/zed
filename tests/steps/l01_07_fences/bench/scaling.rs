//! Extracting fences and reading their marks and labels are of order n log n in the length of
//! the document, and comparing variant fixtures with their fences is linear (DESIGN.md Part G,
//! item VARIANT-sync): the benchmarks of this step, run by `tools/run_tests.sh --bench`.
//! `scaling.rs` makes each of their checks at small sizes.

use zed_tests::scaling::{check, inputs};

use crate::scaling::{
    agree, extracts_each_fence_with_its_mark_and_label, extracts_its_marks_and_label, many_fences,
    one_long_fence, one_long_variant, variants_with_their_fences,
};

#[test]
fn many_fences_scale() {
    let docs = inputs(1_000, many_fences);
    check(
        "extracting n fences with their marks and labels",
        1_000,
        |n| extracts_each_fence_with_its_mark_and_label(&docs[&n], n),
    );
}

#[test]
fn one_long_fence_scales() {
    let docs = inputs(2_000, one_long_fence);
    check(
        "extracting a fence of 2n lines with its marks and label",
        2_000,
        |n| extracts_its_marks_and_label(&docs[&n], n),
    );
}

#[test]
fn comparing_n_variants_with_their_fences_scales() {
    let made = inputs(1_000, variants_with_their_fences);
    check(
        "comparing n variant fixtures with their fences",
        1_000,
        |n| agree(&made[&n]),
    );
}

#[test]
fn comparing_one_long_variant_scales() {
    let made = inputs(2_000, one_long_variant);
    check(
        "comparing a variant fixture of 2n lines with its fence",
        2_000,
        |n| agree(&made[&n]),
    );
}
