//! Completeness tests (TEST-complete-reduced, author P189): the four words in each position a
//! value may take, on each kind of text DESIGN names, and beside the features they meet.

use super::{accepted, rejected, x};

/// Whether every row of the test tables of `src` passes.
fn rows_pass(src: &str) -> bool {
    let out = zedc::testing::test(src);
    let failures: Vec<_> = out.iter().filter_map(|o| o.failure.as_ref()).collect();
    assert!(failures.is_empty(), "{src}\n{failures:?}");
    !out.is_empty()
}

#[test]
fn escapes_controls_and_noncharacters_are_scalars() {
    for (text, n) in [
        ("\\u{0}", "0"),
        ("\\n", "10"),
        ("\\t", "9"),
        ("\\\\", "92"),
        ("\\\"", "34"),
        ("\\u{7F}", "127"),
        ("\\u{FEFF}", "65279"),
        ("\\u{FFFE}", "65534"),
        ("\\u{FFFF}", "65535"),
        ("\\u{1F600}", "128512"),
        ("\\u{10FFFF}", "1114111"),
    ] {
        assert_eq!(x(&format!("codePoint(\"{text}\")")), n, "{text}");
    }
    // The noncharacters are scalar values, so `scalar` gives them.
    for n in ["65534", "65535", "1114110"] {
        assert_eq!(x(&format!("codePoint(scalar({n}))")), n, "{n}");
    }
}

#[test]
fn a_combining_sequence_is_two_scalars() {
    // `e` and U+0301 COMBINING ACUTE ACCENT read as one letter and are two code points.
    assert_eq!(x("codePoint(text(\"e\\u{301}\"))"), "#notScalar");
    assert_eq!(x("utf8(\"e\\u{301}\")"), "{0 -> 101, 1 -> 204, 2 -> 129}");
    assert_eq!(x("utf8(\"é\") == utf8(\"e\\u{301}\")"), "false");
}

#[test]
fn utf8_of_controls_and_the_last_scalar() {
    // The one byte 0: its printed form (a family mapping its one key to itself) is the
    // printer's; reading it by key is lookup, step L3.2. The round trip below holds it.
    assert_eq!(x("utf8(\"a\\nb\")"), "{0 -> 97, 1 -> 10, 2 -> 98}");
    assert_eq!(
        x("utf8(\"\\u{10FFFF}\")"),
        "{0 -> 244, 1 -> 143, 2 -> 191, 3 -> 191}"
    );
    assert_eq!(x("fromUtf8(utf8(\"\\u{0}\")) == \"\\u{0}\""), "true");
}

#[test]
fn each_word_in_other_positions() {
    // A tuple component, nested words, a comparison, an arithmetic operand, a lambda body,
    // a function's value passed on, and the bytes compared as values.
    assert_eq!(x("(codePoint(\"a\"), codePoint(\"b\"))"), "(97, 98)");
    assert_eq!(x("codePoint(scalar(codePoint(\"é\")))"), "233");
    assert_eq!(x("codePoint(\"a\") < codePoint(\"b\")"), "true");
    assert_eq!(x("codePoint(\"b\") - codePoint(\"a\")"), "1");
    assert_eq!(x("utf8(\"ab\") == utf8(\"a\" ++ \"b\")"), "true");
    assert_eq!(
        x("fromUtf8(utf8(\"a\")) ++ fromUtf8(utf8(\"b\"))"),
        "\"ab\""
    );
    let lambda = "cp = s -> codePoint(s);\nback = n -> scalar(n);\n";
    let v = |src: &str, name| zed_tests::step_helpers::l01_16_elaboration::value(src, name);
    assert_eq!(v(&format!("{lambda}x = cp(\"z\");\n"), "x"), "122");
    assert_eq!(v(&format!("{lambda}x = back(122);\n"), "x"), "\"z\"");
    assert_eq!(v(&format!("{lambda}x = cp(\"zz\");\n"), "x"), "#notScalar");
}

#[test]
fn each_word_in_a_function_body_under_test_tables() {
    for src in [
        "lead(positional s: String) = codePoint(s) else -1\n\
         test { \"a\" -> 97, \"é\" -> 233, \"\" -> -1, \"ab\" -> -1 }\n",
        "glyph(positional n: int) = scalar(n) else \"?\"\n\
         test { 65 -> \"A\", -1 -> \"?\", 55296 -> \"?\", 1114112 -> \"?\" }\n",
        "same(positional s: String) = fromUtf8(utf8(s)) == s\n\
         test { \"\" -> true, \"a😀\" -> true }\n",
        // An `if` branch.
        "g(positional n: int) = if n >= 0 { scalar(n) else \"?\" } else { \"-\" }\n\
         test { 97 -> \"a\", -5 -> \"-\", 57343 -> \"?\" }\n",
    ] {
        assert!(rows_pass(src), "{src}");
    }
}

#[test]
fn a_failure_atom_as_the_argument_passes_through() {
    let src = "pick(positional b: bool) = if b { \"a\" } else { #none };\n\
               n(positional b: bool) = if b { 97 } else { #none };\n\
               c = codePoint(pick(false));\n\
               s = scalar(n(false));\n\
               u = utf8(pick(false));\n\
               ok = codePoint(pick(true));\n";
    let v = |name| zed_tests::step_helpers::l01_16_elaboration::value(src, name);
    assert_eq!(v("c"), "#none");
    assert_eq!(v("s"), "#none");
    assert_eq!(v("u"), "#none");
    assert_eq!(v("ok"), "97");
}

#[test]
fn an_argument_of_another_kind_is_rejected() {
    for src in [
        "x = codePoint(true);\n",
        "x = codePoint((\"a\", \"b\"));\n",
        "x = scalar(1/2);\n",
        "x = scalar(65.0f64);\n",
        "x = scalar(\"65\");\n",
        "x = utf8(97);\n",
        "x = utf8(true);\n",
        "x = fromUtf8(97);\n",
        "x = fromUtf8(\"a\");\n",
    ] {
        let out = rejected(src);
        let word = &src[4..src.find('(').unwrap()];
        let at_word = out.contains(&format!("`{word}` does not take"));
        assert!(at_word || out.contains("f64`, never `int`"), "{src}: {out}");
    }
}

#[test]
fn the_words_take_one_positional_argument() {
    for src in [
        "x = codePoint();\n",
        "x = codePoint(\"a\", \"b\");\n",
        "x = scalar(65, 66);\n",
        "x = utf8();\n",
        "x = fromUtf8(utf8(\"a\"), utf8(\"b\"));\n",
    ] {
        let out = rejected(src);
        let word = &src[4..src.find('(').unwrap()];
        assert!(out.contains(&format!("`{word}`")), "{src}: {out}");
    }
    // One parameter takes its argument in either form (sec:values_morphisms) only when it has a
    // name; the prelude words are declared positional, so the bare forms are the only ones.
    assert!(accepted("x = codePoint(\"a\");\n"));
}
