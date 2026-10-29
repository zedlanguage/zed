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
