//! Extracting fences and reading their marks and labels are of order n log n in the length of
//! the document (DESIGN.md Part G).

use zed_tests::scaling::{check, inputs};
use zedc::fence::{extract, label, marks};

#[test]
fn many_fences_scale() {
    let one = "Text.\n\n```zed\n// layer L3\nx = 1;   // \u{2717} no\n\
               // y = 2; // \u{2717} variant\n```\n";
    let docs = inputs(1_000, |n| one.repeat(n));
    check(
        "extracting n fences with their marks and labels",
        1_000,
        |n| {
            let fences = extract(&docs[&n]);
            assert_eq!(fences.len(), n);
            for f in &fences {
                assert_eq!((marks(&f.text).lines.len(), label(&f.text)), (1, Some(3)));
            }
        },
    );
}

#[test]
fn one_long_fence_scales() {
    let docs = inputs(2_000, |n| {
        format!("```zed\n{}", "// layer L2\nx = 1; // \u{2717}\n".repeat(n))
    });
    check(
        "extracting a fence of 2n lines with its marks and label",
        2_000,
        |n| {
            let fences = extract(&docs[&n]);
            let f = &fences[0];
            assert_eq!((marks(&f.text).lines.len(), label(&f.text)), (n, Some(2)));
        },
    );
}
