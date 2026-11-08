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

/// n fences with a commented ✗ line each, and a fixture of each: comparing them is linear
/// (item VARIANT-sync).
#[test]
fn comparing_n_variants_with_their_fences_scales() {
    use zed_tests::fences::{DocFence, Variant, disagreements};

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
        let variants: Vec<Variant> = (0..n)
            .map(|i| {
                let of = format!("// b{i} = a{i} + x;   // \u{2717} no x");
                Variant {
                    name: format!("v{i}"),
                    text: format!(
                        "// variant: {of}\na{i} = 1;\nb{i} = a{i} + x;   // \u{2717} no x\nc{i} = 2;\n"
                    ),
                    of,
                }
            })
            .collect();
        (fences, variants)
    });
    check(
        "comparing n variant fixtures with their fences",
        1_000,
        |n| {
            let (fences, variants) = &made[&n];
            assert_eq!(disagreements(fences, variants, &[]), [""; 0]);
        },
    );
}

/// One fence of n lines and its fixture: comparing them is linear in n.
#[test]
fn comparing_one_long_variant_scales() {
    use zed_tests::fences::{DocFence, Variant, disagreements};

    let made = inputs(2_000, |n| {
        let lines: String = (0..n).map(|i| format!("a{i} = {i};\n")).collect();
        let of = "// b = x;   // \u{2717} no x";
        let fence = DocFence {
            key: "DESIGN.md [sec:grammar] 1".into(),
            at: "DESIGN.md:1".into(),
            layer: 1,
            ring: 1,
            notation: false,
            // A fence from `extract` ends without a line break.
            text: format!("{lines}{of}\n{lines}").trim_end().into(),
        };
        let variant = Variant {
            name: "v".into(),
            of: of.into(),
            text: format!("// variant: {of}\n{lines}b = x;   // \u{2717} no x\n{lines}"),
        };
        (vec![fence], vec![variant])
    });
    check(
        "comparing a variant fixture of 2n lines with its fence",
        2_000,
        |n| {
            let (fences, variants) = &made[&n];
            assert_eq!(disagreements(fences, variants, &[]), [""; 0]);
        },
    );
}
