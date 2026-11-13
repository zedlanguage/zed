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

/// n fences with a commented ✗ line each, and a table entry for each: building the variants is
/// linear in the table and the fences (item SPEC-no-verbatim).
#[test]
fn building_n_variants_scales() {
    use zed_tests::fences::{DocFence, build};

    let made = inputs(1_000, |n| {
        let fences: Vec<DocFence> = (0..n)
            .map(|i| DocFence {
                key: format!("DESIGN.md [sec:grammar] {i}"),
                at: format!("DESIGN.md:{}", 5 * i + 1),
                layer: 1,
                ring: 1,
                notation: false,
                text: format!("a{i} = 1;\n// b{i} = a{i} + x;   // \u{2717} no x\nc{i} = 2;"),
            })
            .collect();
        let table: String = (0..n)
            .map(|i| {
                format!(
                    "variant: v{i}\nfence: DESIGN.md [sec:grammar] {i}\nlive: b{i} =\n\
                     edit: c{i} = 2 => c{i} = 3\n"
                )
            })
            .collect();
        (fences, table)
    });
    check("building n variants from n fences", 1_000, |n| {
        let (fences, table) = &made[&n];
        assert_eq!(build(table, fences).expect("variants").len(), n);
    });
}

/// One fence of n lines, and a variant that leaves out one of them and edits another: building
/// it is linear in n.
#[test]
fn building_one_long_variant_scales() {
    use zed_tests::fences::{DocFence, build};

    let made = inputs(2_000, |n| {
        let lines: String = (0..n).map(|i| format!("a{i} = {i};\n")).collect();
        let more: String = (0..n).map(|i| format!("c{i} = {i};\n")).collect();
        let fence = DocFence {
            key: "DESIGN.md [sec:grammar] 1".into(),
            at: "DESIGN.md:1".into(),
            layer: 1,
            ring: 1,
            notation: false,
            // A fence from `extract` ends without a line break.
            text: format!("{lines}// b = x;   // \u{2717} no x\n{more}z = 0;"),
        };
        let table = "variant: v\nfence: DESIGN.md [sec:grammar] 1\nlive: b = x\nomit: z = 0\nedit: a0 = 0; => a0 = 1;"
            .to_string();
        (vec![fence], table)
    });
    check("building a variant of a fence of 2n lines", 2_000, |n| {
        let (fences, table) = &made[&n];
        let v = build(table, fences).expect("a variant");
        assert_eq!(v[0].text.lines().count(), 2 * n + 2);
    });
}
