//! The completeness pass over DIAG-control (row TEST-complete-diagnostics): the cases
//! COMPLETENESS.md lists that `mod.rs` leaves out. Expected results are from DESIGN.md
//! sec:diagnostics, "Characters a terminal does not show".

use zed_kernel::Value;
use zedc::check::read::parse_type;
use zedc::check::ty::Ty;
use zedc::front::{Diagnostic, Step};
use zedc::terminal::{Escaped, escape_width, hidden};

use super::{raw, rejected};

/// The rejection of `greet = "<inner>" ++ 3;`, `inner` as the source holds it.
fn greet(inner: &str) -> String {
    rejected(&format!(
        "greet = \"{inner}\" ++ 3;\nmain(m: MainArgs) = 0;\n"
    ))
}

#[test]
fn every_kind_of_hidden_character_prints_escaped_in_the_line_and_the_type() {
    // One of each kind DESIGN names: a C0 control, the C1 control NEL (also a space), a space
    // other than U+0020, a line separator, a zero-width space, a joiner, a byte order mark,
    // each bidirectional control, and a format character above U+FFFF (a tag).
    for (c, form) in [
        ('\u{7}', "\\u{7}"),
        ('\u{85}', "\\u{85}"),
        ('\u{2003}', "\\u{2003}"),
        ('\u{2028}', "\\u{2028}"),
        ('\u{2029}', "\\u{2029}"),
        ('\u{200B}', "\\u{200B}"),
        ('\u{200D}', "\\u{200D}"),
        ('\u{FEFF}', "\\u{FEFF}"),
        ('\u{202A}', "\\u{202A}"),
        ('\u{202E}', "\\u{202E}"),
        ('\u{2066}', "\\u{2066}"),
        ('\u{2069}', "\\u{2069}"),
        ('\u{E0001}', "\\u{E0001}"),
    ] {
        let out = greet(&format!("a{c}b"));
        assert_eq!(raw(&out), None, "{:X}: {out:?}", c as u32);
        assert!(
            out.contains(&format!("this expression is \"a{form}b\"")),
            "{:X}, the printed type: {out}",
            c as u32
        );
        assert!(
            out.contains(&format!("1 | greet = \"a{form}b\" ++ 3;")),
            "{:X}, the quoted line: {out}",
            c as u32
        );
    }
}

#[test]
fn the_marks_stand_under_a_literal_holding_a_five_digit_escape() {
    // `"a\u{E0001}b"` is 1 + 1 + 9 + 1 + 1 = 13 columns.
    let out = greet("a\u{E0001}b");
    assert!(
        out.contains(&format!("\n        |         {} [1]\n", "^".repeat(13))),
        "{out}"
    );
}

#[test]
fn private_unassigned_and_noncharacter_code_points_print_escaped_in_a_type() {
    // None is a control, a space or of no width, so the quoted line shows each as itself; the
    // printed type, a Zed literal, writes each in its escape form and reads back as itself.
    for (c, form) in [
        ('\u{E000}', "\\u{E000}"),
        ('\u{378}', "\\u{378}"),
        ('\u{FFFF}', "\\u{FFFF}"),
        ('\u{10FFFF}', "\\u{10FFFF}"),
    ] {
        let t = Ty::lit(&Value::str(&format!("a{c}b")));
        let text = t.to_string();
        assert_eq!(text, format!("\"a{form}b\""), "{:X}", c as u32);
        assert_eq!(parse_type(&text), Ok(t), "{text}");
    }
}

#[test]
fn a_string_type_with_no_special_character_prints_as_written() {
    for s in ["", "abc", "a'b", "a$b", "$", "{}", "日本"] {
        let t = Ty::lit(&Value::str(s));
        let text = t.to_string();
        assert_eq!(text, format!("\"{s}\""));
        assert_eq!(parse_type(&text), Ok(t));
    }
    // A `$` at the end, and one before a `$`, start no hole.
    let t = Ty::lit(&Value::str("a$$"));
    assert_eq!(t.to_string(), "\"a$$\"");
    // `${` at the start, twice in a row.
    let t = Ty::lit(&Value::str("${${"));
    assert_eq!(t.to_string(), "\"\\${\\${\"");
    assert_eq!(parse_type(&t.to_string()), Ok(t));
}

#[test]
fn an_escape_in_a_comment_on_a_quoted_line_prints_escaped() {
    let out = rejected("greet = \"a\" ++ 3; // \u{1B}[2J\nmain(m: MainArgs) = 0;\n");
    assert_eq!(raw(&out), None, "{out:?}");
    assert!(
        out.contains("1 | greet = \"a\" ++ 3; // \\u{1B}[2J"),
        "{out}"
    );
}

#[test]
fn hidden_characters_on_two_lines_print_escaped_on_each() {
    let out =
        rejected("greet = \"\u{1B}x\" ++ 3;\nwave = \"\u{202E}y\" ++ 4;\nmain(m: MainArgs) = 0;\n");
    assert_eq!(raw(&out), None, "{out:?}");
    assert!(out.contains("1 | greet = \"\\u{1B}x\" ++ 3;"), "{out}");
    assert!(out.contains("2 | wave = \"\\u{202E}y\" ++ 4;"), "{out}");
}

#[test]
fn a_line_feed_lays_out_a_message_and_a_tab_in_a_message_is_kept() {
    // A message's own line breaks are the layout; a tab is not a hidden character.
    assert_eq!(Escaped("a\nb\tc").to_string(), "a\nb\tc");
    // A lone CR and a CR before a line feed are both escaped: only the line feed lays out.
    assert_eq!(Escaped("a\r\nb\rc").to_string(), "a\\u{D}\nb\\u{D}c");
    // Text with nothing hidden is written as it is.
    assert_eq!(Escaped("é日😀").to_string(), "é日😀");
    assert_eq!(Escaped("").to_string(), "");
    // At the start and at the end.
    assert_eq!(Escaped("\u{1B}a\u{1B}").to_string(), "\\u{1B}a\\u{1B}");
}

#[test]
fn the_width_of_an_escape_is_counted_for_every_digit_count() {
    for (c, w) in [
        ('\u{0}', 5),
        ('\u{F}', 5),
        ('\u{10}', 6),
        ('\u{FF}', 6),
        ('\u{100}', 7),
        ('\u{FFF}', 7),
        ('\u{1000}', 8),
        ('\u{FFFF}', 8),
        ('\u{10000}', 9),
        ('\u{10FFFF}', 10),
    ] {
        assert_eq!(escape_width(c), w, "{:X}", c as u32);
    }
}

#[test]
fn a_combining_mark_shows_and_a_format_character_does_not() {
    // Marks of three scripts show on the character before them.
    for c in ['\u{301}', '\u{94D}', '\u{5B4}', '\u{20DD}'] {
        assert!(!hidden(c), "{:X}", c as u32);
    }
    // The Arabic letter mark, the Mongolian vowel separator, the word joiner and the
    // invisible times are format characters of no width.
    for c in ['\u{61C}', '\u{180E}', '\u{2060}', '\u{2062}'] {
        assert!(hidden(c), "{:X}", c as u32);
    }
}

#[test]
fn a_step_on_another_line_than_the_headline_quotes_its_own_line() {
    let d = Diagnostic {
        row: None,
        address: zedc::address::ContentAddress([0; 32]),
        line: 1,
        col: 1,
        message: "m".into(),
        steps: vec![
            Step {
                line: 1,
                col: 1,
                text: "first".into(),
                source: "a = \"\u{1B}\";".into(),
                width: 1,
            },
            Step {
                line: 2,
                col: 1,
                text: "second \u{202E}".into(),
                source: "b = \"\u{2028}\";".into(),
                width: 1,
            },
        ],
        menu: String::new(),
    };
    let out = d.to_string();
    assert_eq!(raw(&out), None, "{out:?}");
    assert!(out.contains("1 | a = \"\\u{1B}\";"), "{out}");
    assert!(out.contains("[2] 2:1: second \\u{202E}"), "{out}");
    assert!(out.contains("2 | b = \"\\u{2028}\";"), "{out}");
}

#[test]
fn a_combining_mark_in_a_printed_type_is_written_escaped_even_at_the_start() {
    // A string may hold a combining mark with no character before it; the literal writes each
    // one in its escape form, so the printed type shows what the string holds.
    for (s, form) in [
        ("\u{301}", "\"\\u{301}\""),
        ("q\u{301}", "\"q\\u{301}\""),
        ("\u{301}\u{301}", "\"\\u{301}\\u{301}\""),
    ] {
        let t = Ty::lit(&Value::str(s));
        assert_eq!(t.to_string(), form);
        assert_eq!(parse_type(form), Ok(t), "{form}");
    }
}

#[test]
fn a_string_inside_a_value_prints_with_the_same_writer() {
    // `String(x)` of a family holding a key with an ESC and a value with a `${`: the text the
    // program gets writes each string as a Zed literal.
    use zed_kernel::term::build::{lit, prim};
    use zed_kernel::{Family, Prim, eval};
    let f = Family::of([("a\u{1B}[2J", Value::str("${x}\u{200B}"))]);
    let got = eval(&prim(Prim::Show, vec![lit(f)])).unwrap();
    assert_eq!(got, Value::str(r#"{"a\u{1B}[2J" -> "\${x}\u{200B}"}"#));
}
