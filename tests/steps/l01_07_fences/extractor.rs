use zedc::fence::{Fence, Marks, extract, label, marks};

#[test]
fn only_zed_fences_are_extracted_with_their_lines() {
    let md = "# Notes\n\n```peg\nA = 'a'\n```\n\nText.\n\n```zed\nx = 1;\n\ny = x;\n```\n\n```\nplain\n```\n\n1. Step:\n   ```zed\n   z = 2;\n   ```\n";
    assert_eq!(
        extract(md),
        [
            Fence {
                line: 9,
                before: "".into(),
                text: "x = 1;\n\ny = x;".into()
            },
            Fence {
                line: 20,
                before: "1. Step:".into(),
                text: "   z = 2;".into()
            },
        ]
    );
}

#[test]
fn an_unclosed_fence_runs_to_the_end() {
    assert_eq!(extract("```zed\na = 1;\nb = 2;")[0].text, "a = 1;\nb = 2;");
    assert_eq!(extract("```zed\n```")[0].text, "");
}

#[test]
fn a_mark_on_a_comment_line_is_a_variant() {
    let text = "q = Point(x:, y:);\n// q = Point(3.0, 4.0);   // ✗ by name\nz = 7 / 2;   // ✗ `/` is for f64 and rat only\n  // ✗ indented, still a variant";
    assert_eq!(
        marks(text),
        Marks {
            lines: vec![3],
            variants: vec![2, 4]
        }
    );
    assert_eq!(marks("a = 1; // ✓ fine"), Marks::default());
}

#[test]
fn a_label_is_a_whole_comment_line() {
    assert_eq!(label("// [d4] sec:power\n// layer L2\nx = 1;"), Some(2));
    assert_eq!(label("// layer L12 — names a struct of L12"), Some(12));
    assert_eq!(label("// layer L3\n  // layer L5"), Some(5));
    assert_eq!(label("// layer L1x"), None);
    assert_eq!(label("// layered L3"), None);
    assert_eq!(label("x = 1; // layer L3"), None);
}
