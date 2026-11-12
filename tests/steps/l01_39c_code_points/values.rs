//! The cases DESIGN.md step L1.39c names, through the surface, and the forms a lexer writes.

use super::x;

#[test]
fn the_named_code_points() {
    assert_eq!(x("codePoint(\"a\")"), "97");
    assert_eq!(x("codePoint(\"é\")"), "233");
    assert_eq!(x("codePoint(text(\"ab\"))"), "#notScalar");
    assert_eq!(x("codePoint(text(\"\"))"), "#notScalar");
}

#[test]
fn a_surrogate_is_not_a_scalar_and_an_emoji_round_trips() {
    assert_eq!(x("scalar(whole(55296))"), "#notScalar");
    assert_eq!(x("scalar(128512)"), "\"😀\"");
    assert_eq!(x("codePoint(scalar(128512))"), "128512");
}

#[test]
fn scalar_refuses_every_int_that_is_not_a_scalar_value() {
    for n in [
        "-1", "55296", "56000", "57343", "1114112", "2^64", "-(2^70)",
    ] {
        assert_eq!(x(&format!("scalar(whole({n}))")), "#notScalar", "{n}");
    }
    for n in ["0", "55295", "57344", "1114111"] {
        assert_eq!(x(&format!("codePoint(scalar({n}) else \"\")")), n, "{n}");
    }
}

#[test]
fn utf8_gives_the_bytes_keyed_from_zero() {
    assert_eq!(x("utf8(\"aé\")"), "{0 -> 97, 1 -> 195, 2 -> 169}");
    assert_eq!(x("utf8(\"€\")"), "{0 -> 226, 1 -> 130, 2 -> 172}");
    assert_eq!(
        x("utf8(\"😀\")"),
        "{0 -> 240, 1 -> 159, 2 -> 152, 3 -> 128}"
    );
    assert_eq!(x("utf8(\"\")"), "{}");
}

#[test]
fn from_utf8_of_utf8_is_the_string() {
    for s in ["", "a", "naïve", "€ 5", "a😀b"] {
        assert_eq!(x(&format!("fromUtf8(utf8(\"{s}\"))")), format!("\"{s}\""));
        assert_eq!(x(&format!("fromUtf8(utf8(\"{s}\")) == \"{s}\"")), "true");
    }
    // The last scalar prints escaped; the round trip still compares equal.
    assert_eq!(
        x("fromUtf8(utf8(scalar(1114111) else \"\")) == scalar(1114111)"),
        "true"
    );
}

#[test]
fn a_receiver_is_the_string() {
    assert_eq!(x("\"z\".codePoint"), "122");
    assert_eq!(x("\"z\".codePoint()"), "122");
    assert_eq!(x("\"ok\".utf8.fromUtf8"), "\"ok\"");
    assert_eq!(x("955.scalar"), "\"λ\"");
}

#[test]
fn a_rope_is_read_as_its_text() {
    assert_eq!(x("codePoint(\"\" ++ \"é\" ++ \"\")"), "233");
    assert_eq!(x("codePoint(\"a\" ++ \"b\")"), "#notScalar");
    assert_eq!(x("utf8(\"a\" ++ \"é\")"), "{0 -> 97, 1 -> 195, 2 -> 169}");
}

#[test]
fn the_failures_pass_through_else() {
    let src = "text(positional v: String) = v;\n\
               whole(positional v: int) = v;\n\
               digit = codePoint(\"7\") - codePoint(\"0\") else -1;\n\
               none = codePoint(text(\"77\")) else -1;\n\
               shown = scalar(whole(55296)) else \"?\";\n";
    let v = |n| zed_tests::step_helpers::l01_16_elaboration::value(src, n);
    assert_eq!(v("digit"), "7");
    assert_eq!(v("none"), "-1");
    assert_eq!(v("shown"), "\"?\"");
}

/// The form the corpus's UTF-8 decoder writes: a decoded code point interpolated through
/// `scalar`, whose failure for a value that is not a scalar fails the text.
#[test]
fn an_interpolated_scalar_is_its_text_or_its_failure() {
    assert_eq!(x("\"${scalar(65)}\""), "\"A\"");
    assert_eq!(x("\"a${scalar(233)}b\""), "\"aéb\"");
    assert_eq!(x("\"${scalar(whole(56000))}\""), "#notScalar");
    assert_eq!(x("\"${scalar(whole(1114112))}\""), "#notScalar");
}
