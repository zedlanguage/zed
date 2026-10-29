use super::text;
use zedc::lex::lex;

#[test]
fn plain_strings_and_escapes() {
    assert_eq!(text(r#""Hello, world""#), "Hello, world");
    assert_eq!(text(r#""""#), "");
    assert_eq!(text(r#""name\tqty\n""#), "name\tqty\n");
    assert_eq!(text(r#""C:\\Users\\ana""#), r"C:\Users\ana");
    assert_eq!(text(r#""she said \"hi\"""#), r#"she said "hi""#);
    assert_eq!(
        text(r#""price: \$5, \${not a hole}""#),
        "price: $5, ${not a hole}"
    );
    assert_eq!(text(r#""nul\0 cr\r""#), "nul\0 cr\r");
    assert_eq!(text(r#""\u{1F600} \u{e9} \u{0041}""#), "😀 é A");
    // Text in any script, and a comment delimiter in a string is text.
    assert_eq!(
        text(r#""Größe: 面積 // not a comment /* nor this""#),
        "Größe: 面積 // not a comment /* nor this"
    );
}

#[test]
fn a_triple_quoted_string_strips_its_closing_indentation() {
    let sql = "        query = \"\"\"\n            SELECT name, qty\n              FROM stock\n\n             WHERE qty < 10\n            \"\"\"";
    let body = &sql[16..];
    assert_eq!(
        text(body),
        "SELECT name, qty\n  FROM stock\n\n WHERE qty < 10"
    );
}

#[test]
fn stripping_needs_both_delimiters_on_their_own_lines() {
    // Closing delimiter after text: kept as written, the first line break included.
    assert_eq!(text("\"\"\"\n  a\n  b\"\"\""), "\n  a\n  b");
    // Opening delimiter followed by text: kept as written.
    assert_eq!(text("\"\"\"a\n  b\n  \"\"\""), "a\n  b\n  ");
    // A `"""` string may hold quotes and need not span lines; it ends at the first `"""`.
    assert_eq!(
        text(r#""""say "hi" and ""bye"" ok""""#),
        r#"say "hi" and ""bye"" ok"#
    );
}

#[test]
fn blank_lines_and_deeper_lines_inside_a_stripped_string() {
    // A line of fewer spaces than the indentation, or none, is an empty line; a deeper one keeps
    // its extra spaces; tabs are indentation when the closing line uses tabs.
    assert_eq!(
        text("\"\"\"\n    a\n  \n\n      b\n    \"\"\""),
        "a\n\n\n  b"
    );
    assert_eq!(text("\"\"\"\n\tx\n\t\ty\n\t\"\"\""), "x\n\ty");
    // An escape is decoded after stripping, so `\t` and `\n` are text, not indentation.
    assert_eq!(text("\"\"\"\n    \\tx\\n\n    \"\"\""), "\tx\n");
    // Only the delimiters' line breaks: an empty string.
    assert_eq!(text("\"\"\"\n    \"\"\""), "");
}

#[test]
fn golden_malformed_strings() {
    let cases = [
        "\"unclosed",
        "\"two\nlines\"",
        "\"\"\"never closed\n",
        r#""\q is not an escape""#,
        r#""\u{110000}""#,
        r#""\u{D800}""#,
        r#""\u0041""#,
        r#""\u{}""#,
        "\"\"\"\n    in\n  out\n    \"\"\"",
        "\"\"\"\n    in\n\tout\n    \"\"\"",
        r#""ends in a backslash\"#,
    ];
    let out: Vec<String> = cases
        .iter()
        .map(|c| {
            let e = lex(c).unwrap_err();
            format!("{c:?}\n    [{}..{}] {e}", e.span.start, e.span.end)
        })
        .collect();
    insta::assert_snapshot!(out.join("\n"));
}
