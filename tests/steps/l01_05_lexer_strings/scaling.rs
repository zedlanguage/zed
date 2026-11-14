//! The long strings the benchmarks of `bench.rs` lex, and what lexing each must give, checked
//! here at small sizes (TEST-bench-move-rest, P170).

use zedc::lex::lex;

use super::parts;

/// A `"""` string of `n` indented lines, each holding a hole.
pub(super) fn lines(n: usize) -> String {
    let body: String = (0..n).map(|i| format!("    line ${{{i}}}\n")).collect();
    format!("\"\"\"\n{body}    \"\"\"")
}

#[test]
fn an_indented_string_of_lines_with_holes_has_a_text_and_a_hole_a_line() {
    for n in [1, 2, 9] {
        assert_eq!(parts(&lines(n)).len(), 2 * n);
    }
    let p = parts(&lines(2));
    assert_eq!([&p[0][..], &p[2][..]], ["line ", "\nline "]);
    assert!(
        p[1].starts_with("${Int") && p[3].starts_with("${Int"),
        "{p:?}"
    );
}

/// A string whose holes nest `d` deep: `"${"${…"${0}"…}"}"`.
pub(super) fn nested(d: usize) -> String {
    "\"${".repeat(d) + "0" + &"}\"".repeat(d)
}

#[test]
fn nested_holes_lex_as_one_string() {
    for d in [1, 2, 9] {
        assert_eq!(lex(&nested(d)).unwrap().len(), 1);
    }
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

/// `n` lines, each a one-line string whose hole holds a block comment and a `"""` string.
pub(super) fn one_line_holes(n: usize) -> String {
    (0..n)
        .map(|i| format!("\"row ${{x{i} /* cell */ ++ \"\"\"t\"\"\"}}\"\n"))
        .collect()
}

#[test]
fn one_line_holes_with_comments_and_strings_lex_a_string_a_line() {
    for n in [1, 2, 9] {
        assert_eq!(lex(&one_line_holes(n)).unwrap().len(), n);
    }
}
