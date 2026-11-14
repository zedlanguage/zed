//! The long documents and fixtures the benchmarks of `bench.rs` read, and what each must give,
//! checked here at small sizes (TEST-bench-move-rest, P170).

use zed_tests::fences::{DocFence, Variant, disagreements};
use zedc::fence::{extract, label, marks};

/// `n` fences, each with a layer label, a ✗ line and a commented ✗ line.
pub(super) fn many_fences(n: usize) -> String {
    let one = "Text.\n\n```zed\n// layer L3\nx = 1;   // \u{2717} no\n\
               // y = 2; // \u{2717} variant\n```\n";
    one.repeat(n)
}

pub(super) fn extracts_each_fence_with_its_mark_and_label(doc: &str, n: usize) {
    let fences = extract(doc);
    assert_eq!(fences.len(), n);
    for f in &fences {
        assert_eq!((marks(&f.text).lines.len(), label(&f.text)), (1, Some(3)));
    }
}

/// One unclosed fence of `2n` lines, a ✗ on every other line.
pub(super) fn one_long_fence(n: usize) -> String {
    format!("```zed\n{}", "// layer L2\nx = 1; // \u{2717}\n".repeat(n))
}

pub(super) fn extracts_its_marks_and_label(doc: &str, n: usize) {
    let fences = extract(doc);
    let f = &fences[0];
    assert_eq!((marks(&f.text).lines.len(), label(&f.text)), (n, Some(2)));
}

/// `n` fences with a commented ✗ line each, and a fixture of each.
pub(super) fn variants_with_their_fences(n: usize) -> (Vec<DocFence>, Vec<Variant>) {
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
}

/// One fence of `2n + 1` lines and its fixture.
pub(super) fn one_long_variant(n: usize) -> (Vec<DocFence>, Vec<Variant>) {
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
}

/// Each fixture agrees with its fence.
pub(super) fn agree((fences, variants): &(Vec<DocFence>, Vec<Variant>)) {
    assert_eq!(disagreements(fences, variants, &[]), [""; 0]);
}

#[test]
fn each_benchmark_document_reads_as_its_benchmark_expects_at_small_sizes() {
    for n in [1, 2, 9] {
        extracts_each_fence_with_its_mark_and_label(&many_fences(n), n);
        extracts_its_marks_and_label(&one_long_fence(n), n);
        agree(&variants_with_their_fences(n));
        agree(&one_long_variant(n));
    }
}
