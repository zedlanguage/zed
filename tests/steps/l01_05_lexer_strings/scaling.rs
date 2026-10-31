//! The lexing of strings at the rule of low complexity (DESIGN.md Part G).

use zed_tests::scaling;

use super::parts;

/// A `"""` string of `n` indented lines, each holding a hole.
fn lines(n: usize) -> String {
    let body: String = (0..n).map(|i| format!("    line ${{{i}}}\n")).collect();
    format!("\"\"\"\n{body}    \"\"\"")
}

#[test]
fn a_long_indented_string_scales() {
    // Each character was tested against every line's cut of indentation.
    scaling::check("a \"\"\" string of n lines", 1000, |n| {
        assert_eq!(parts(&lines(n)).len(), 2 * n);
    });
    let p = parts(&lines(2));
    assert_eq!([&p[0][..], &p[2][..]], ["line ", "\nline "]);
    assert!(
        p[1].starts_with("${Int") && p[3].starts_with("${Int"),
        "{p:?}"
    );
}
