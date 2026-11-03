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
fn golden_malformed_holes() {
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

#[test]
fn a_hole_of_a_one_line_string_holds_no_line_break() {
    // A `//` comment runs to the end of the line, so it takes the `}` with it, and a line break
    // before the `}` does not help: the hole would then hold the line break.
    assert_eq!(
        error("log(\"total: ${sum // all rows\n}\");"),
        "\"// all rows\": malformed string: a `//` comment in a hole of a `\"` string runs to \
         the end of the line, past the `}`; write `/* … */`"
    );
    assert_eq!(
        error("log(\"total: ${sum /* all\n rows */}\");"),
        "\"/* all\": malformed string: a `/* … */` comment in a hole of a `\"` string closes on \
         its line"
    );
    // A block comment nested in another is part of it.
    assert_eq!(
        error("log(\"${sum /* all /* the\n rows */ */}\");"),
        "\"/* all /* the\": malformed string: a `/* … */` comment in a hole of a `\"` string \
         closes on its line"
    );
    assert_eq!(
        error("log(\"total: ${sum +\n tax}\");"),
        "\"${sum +\": malformed string: a hole in a `\"` string closes on its line"
    );
    assert_eq!(
        error("log(\"${{ t = sum + tax;\n t }}\");"),
        "\"${{ t = sum + tax;\": malformed string: a hole in a `\"` string closes on its line"
    );
    assert_eq!(
        error("log(\"${\"\"\"a\nb\"\"\" ++ name}\");"),
        "\"\\\"\\\"\\\"a\": malformed string: a `\"\"\"` string in a hole of a `\"` string \
         closes on its line"
    );
    // A `"""` string in a hole of a `"` string closes on its line, so its own holes do too.
    assert_eq!(
        error("log(\"${\"\"\"${a /* c\n */}\"\"\"}\");"),
        "\"/* c\": malformed string: a `/* … */` comment in a hole of a `\"` string closes on \
         its line"
    );
    assert_eq!(
        error("x = \"${\"\"\"${a // c}\"\"\"}\";\n"),
        "\"// c}\\\"\\\"\\\"}\\\";\": malformed string: a `//` comment in a hole of a `\"` string \
         runs to the end of the line, past the `}`; write `/* … */`"
    );
    // A line break and a later `}"""}` do not end that `//` comment's hole either.
    assert_eq!(
        error("x = \"${\"\"\"${a // c\n}\"\"\"}\";"),
        "\"// c\": malformed string: a `//` comment in a hole of a `\"` string runs to the end of \
         the line, past the `}`; write `/* … */`"
    );
    assert_eq!(
        error("x = \"${\"\"\"${a\n}\"\"\"}\";"),
        "\"${a\": malformed string: a hole in a `\"` string closes on its line"
    );
    // A `"` string in a `"""` string's hole is one-line again.
    assert_eq!(
        error("log(\"\"\"${\"${a /* c\n */}\"}\"\"\");"),
        "\"/* c\": malformed string: a `/* … */` comment in a hole of a `\"` string closes on \
         its line"
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
