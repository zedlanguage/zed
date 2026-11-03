//! The lexing of strings at the rule of low complexity (DESIGN.md Part G).

use std::collections::HashMap;

use zed_tests::scaling;
use zedc::lex::lex;

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

/// A string whose holes nest `d` deep: `"${"${…"${0}"…}"}"`.
fn nested(d: usize) -> String {
    "\"${".repeat(d) + "0" + &"}\"".repeat(d)
}

#[test]
fn nested_holes_scale() {
    // Each hole was scanned for its `}` once for each hole around it, and its text searched
    // for a line break as many times.
    let texts: HashMap<usize, String> = [2_000, 16_000]
        .into_iter()
        .map(|d| (d, nested(d)))
        .collect();
    scaling::check("a string with holes nested d deep", 2_000, |d| {
        assert_eq!(lex(&texts[&d]).unwrap().len(), 1);
    });
    assert_eq!(
        parts(&nested(2)),
        [
            "${Str([Hole { tokens: [Token { tok: Int { radix: 10, digits: \"0\" }, span: Span { start: 6, end: 7 } }], span: Span { start: 4, end: 8 } }])}"
        ]
    );
}

/// Tokens nest as their holes do, so what is done to them holds no thread stack.
#[test]
fn deep_tokens_compare_print_and_drop() {
    let text = nested(100_000);
    let (a, b) = (lex(&text).unwrap(), lex(&text).unwrap());
    assert_eq!(a, b);
    let other = lex(&text.replace('0', "1")).unwrap();
    assert_ne!(a, other);
    assert!(format!("{a:?}").matches("Hole").count() == 100_000);
}

#[test]
fn an_open_hole_at_the_bottom_of_a_deep_nest_is_reported() {
    let text = "\"${".repeat(100_000);
    assert_eq!(lex(&text).unwrap_err().span.start, text.len() - 2);
}
