use super::parts;
use zedc::lex::{Part, Tok, lex};

#[test]
fn a_hole_splits_the_string_and_holds_tokens() {
    assert_eq!(
        parts(r#""Hello, ${name}!""#),
        ["Hello, ", r#"${Name("name")}"#, "!"]
    );
    assert_eq!(parts(r#""${count}""#), [r#"${Name("count")}"#]);
    assert_eq!(
        parts(r#""${a}${b}""#),
        [r#"${Name("a")}"#, r#"${Name("b")}"#]
    );
    assert_eq!(
        parts(r#""total ${1_000}""#),
        ["total ", r#"${Int { radix: 10, digits: "1000" }}"#]
    );
}

#[test]
fn a_string_or_comment_inside_a_hole_follows_its_own_rules() {
    // The `}` in the inner string and the comment do not close the hole.
    assert_eq!(
        parts(r#""tag: ${label "}" /* } */}.""#),
        ["tag: ", r#"${Name("label") Str([Text("}")])}"#, "."]
    );
    // A hole inside a string inside a hole.
    assert_eq!(
        parts(r#""a ${"b ${c}"}""#),
        [
            "a ",
            r#"${Str([Text("b "), Hole { tokens: [Token { tok: Name("c"), span: Span { start: 10, end: 11 } }], span: Span { start: 8, end: 12 } }])}"#
        ]
    );
}

#[test]
fn hole_token_spans_index_the_whole_file() {
    let src = r#"greeting "Hi ${who}""#;
    let toks = lex(src).unwrap();
    let Tok::Str(p) = &toks[1].tok else { panic!() };
    let Part::Hole { tokens, span } = &p[1] else {
        panic!()
    };
    assert_eq!(&src[span.start..span.end], "${who}");
    assert_eq!(&src[tokens[0].span.start..tokens[0].span.end], "who");
    assert_eq!(&src[toks[1].span.start..toks[1].span.end], r#""Hi ${who}""#);
}

#[test]
fn a_hole_in_a_triple_quoted_string_may_span_lines_and_is_not_stripped() {
    let src = "\"\"\"\n    id: ${\n  user // the account\n    }\n    \"\"\"";
    assert_eq!(parts(src), ["id: ", r#"${Name("user")}"#]);
}

#[test]
fn expected_malformed_holes() {
    let cases = [
        r#""${name""#,
        r#""${x // c}""#,
        "\"${x\n}\"",
        r#""${"inner}""#,
        r#""${x /* open }""#,
        "\"\"\"\n  ${x}\n    \"\"\"",
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

/// The error lexing `text` gives, with the text of its span.
fn error(text: &str) -> String {
    let e = lex(text).unwrap_err();
    format!("{:?}: {e}", &text[e.span.start..e.span.end])
}

/// The message for a `/* … */` comment in a hole of a `"` string that does not close on its line.
macro_rules! comment_in_hole {
    () => {
        "this `/* … */` comment is inside a `${…}` hole of a `\"` string, and everything in that \
         hole ends on the line of the `\"` string, which is one line. Close the comment on this \
         line, or move it out of the string."
    };
}

/// The message for a `"""` string in a hole of a `"` string that does not close on its line.
macro_rules! triple_in_hole {
    () => {
        "this `\"\"\"` string is inside a `${…}` hole of a `\"` string, and everything in that \
         hole ends on the line of the `\"` string, which is one line. Close the `\"\"\"` string \
         on this line, or make the outer string a `\"\"\"` string."
    };
}

/// The message for a hole of a `"` string that reaches the end of its line.
macro_rules! open_hole {
    () => {
        "this `${` hole of a `\"` string reaches the end of the line without its closing `}`, and \
         a `\"` string, with its holes, is one line. Write the `}` on this line, or make the \
         string a `\"\"\"` string, which may run over several lines."
    };
}

/// The message for a `//` comment in a hole of a `"` string.
macro_rules! line_comment {
    () => {
        "this `//` comment is inside a `${…}` hole of a `\"` string, and a `//` comment runs to \
         the end of the line, past the `}` that closes the hole. Write the comment as `/* … */`, \
         or move it out of the string."
    };
}

#[test]
fn a_hole_of_a_one_line_string_holds_no_line_break() {
    // A `//` comment runs to the end of the line, so it takes the `}` with it, and a line break
    // before the `}` does not help: the hole would then hold the line break.
    assert_eq!(
        error("log(\"total: ${sum // all rows\n}\");"),
        concat!("\"// all rows\": ", line_comment!())
    );
    assert_eq!(
        error("log(\"total: ${sum /* all\n rows */}\");"),
        concat!("\"/* all\": ", comment_in_hole!())
    );
    // A block comment nested in another is part of it.
    assert_eq!(
        error("log(\"${sum /* all /* the\n rows */ */}\");"),
        concat!("\"/* all /* the\": ", comment_in_hole!())
    );
    assert_eq!(
        error("log(\"total: ${sum +\n tax}\");"),
        concat!("\"${sum +\": ", open_hole!())
    );
    assert_eq!(
        error("log(\"${{ t = sum + tax;\n t }}\");"),
        concat!("\"${{ t = sum + tax;\": ", open_hole!())
    );
    assert_eq!(
        error("log(\"${\"\"\"a\nb\"\"\" ++ name}\");"),
        concat!("\"\\\"\\\"\\\"a\": ", triple_in_hole!())
    );
    // A `"""` string in a hole of a `"` string closes on its line, so its own holes do too.
    assert_eq!(
        error("log(\"${\"\"\"${a /* c\n */}\"\"\"}\");"),
        concat!("\"/* c\": ", comment_in_hole!())
    );
    assert_eq!(
        error("x = \"${\"\"\"${a // c}\"\"\"}\";\n"),
        concat!("\"// c}\\\"\\\"\\\"}\\\";\": ", line_comment!())
    );
    // A line break and a later `}"""}` do not end that `//` comment's hole either.
    assert_eq!(
        error("x = \"${\"\"\"${a // c\n}\"\"\"}\";"),
        concat!("\"// c\": ", line_comment!())
    );
    assert_eq!(
        error("x = \"${\"\"\"${a\n}\"\"\"}\";"),
        concat!("\"${a\": ", open_hole!())
    );
    // A `"` string in a `"""` string's hole is one-line again.
    assert_eq!(
        error("log(\"\"\"${\"${a /* c\n */}\"}\"\"\");"),
        concat!("\"/* c\": ", comment_in_hole!())
    );
}

#[test]
fn a_hole_of_a_one_line_string_may_hold_what_closes_on_its_line() {
    assert_eq!(
        parts(r#""total: ${sum /* all /* the */ rows */ + tax}""#),
        ["total: ", r#"${Name("sum") Op("+") Name("tax")}"#]
    );
    assert_eq!(
        parts(r#""${"""a""" ++ name}""#),
        [r#"${Str([Text("a")]) Op("++") Name("name")}"#]
    );
}

#[test]
fn a_hole_of_a_multi_line_string_may_span_lines() {
    let src = "\"\"\"${sum // all rows\n + tax /* and\n fees */}\"\"\"";
    assert_eq!(parts(src), [r#"${Name("sum") Op("+") Name("tax")}"#]);
}
