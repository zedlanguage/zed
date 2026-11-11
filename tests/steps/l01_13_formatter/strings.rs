//! The formatter on string literals (test audit 2026-11-08, row 9). DESIGN.md sec:lexical: a
//! `"""` string "strips the indentation of its closing delimiter", "escapes are decoded after
//! stripping", "any other `"""` string is kept as written", and "Line endings normalize to `\n`:
//! `\r\n` and a lone `\r` are each one line break". The formatter moves the code around a string
//! to a new indentation, so each test checks that every string's value is unchanged, that the
//! text the formatter writes is a fixed point (step L1.13's standing rule), and the text itself.
//! Each runs `format_source`, the function `zedc fmt` runs, on the file's bytes.

use zed_tests::step_helpers::l01_19_whole_file_ports::run;
use zedc::format::format_source;
use zedc::lex::{Part, Tok, Token};

/// The value of each string literal of the file `bytes`, in source order: its decoded text,
/// with each hole written `${}`, and after it the values of the strings inside its holes.
fn values(bytes: &[u8]) -> Vec<String> {
    let text = zedc::source::load(bytes).unwrap();
    let tokens = zedc::lex::lex(&text).unwrap();
    let mut out = Vec::new();
    collect(&tokens, &mut out);
    out
}

/// Appends to `out` the values of the strings among `tokens`, as [`values`] orders them.
fn collect(tokens: &[Token], out: &mut Vec<String>) {
    for t in tokens {
        if let Tok::Str(parts) = &t.tok {
            let mut value = String::new();
            let mut inner = Vec::new();
            for p in parts {
                match p {
                    Part::Text(s) => value += s,
                    Part::Hole { tokens, .. } => {
                        value += "${}";
                        collect(tokens, &mut inner);
                    }
                }
            }
            out.push(value);
            out.append(&mut inner);
        }
    }
}

/// The file `bytes` formatted, after checking that the result formats to itself and that its
/// strings have the values of the source's strings, which are `want`.
#[track_caller]
fn fmt_strings(bytes: &[u8], want: &[&str]) -> String {
    assert_eq!(values(bytes), want, "the source's strings");
    let out = format_source(bytes).unwrap();
    assert_eq!(
        values(out.as_bytes()),
        want,
        "the strings changed in\n{out}"
    );
    assert_eq!(
        format_source(out.as_bytes()).unwrap(),
        out,
        "not a fixed point"
    );
    // The standing rule of step L1.13 too: the source, its line ends normalized, formats to the
    // same text, with the same statements and the same comments.
    assert_eq!(super::fmt(&zedc::source::load(bytes).unwrap()), out);
    out
}

/// A `"""` string two blocks deep, written at an indentation the formatter changes: the
/// statements around it move to two spaces per level, and the string, whose lines lose the
/// indentation of its closing delimiter, is written as it was spelled, so each of its lines
/// keeps the same text after stripping. A blank line in the string and a line indented further
/// than the delimiter are kept.
#[test]
fn a_triple_quoted_string_two_blocks_deep_keeps_its_value() {
    let src = r#"poem(n){
        if n==0 {
                    t = """
                        first line
                          two more spaces

                        last line
                        """;
                    t
        } else {"none"}
}
main(m: MainArgs) { m.stdout <- poem(n: 0); }
"#;
    let want = "first line\n  two more spaces\n\nlast line";
    let out = fmt_strings(src.as_bytes(), &[want, "none"]);
    assert_eq!(
        out,
        r#"poem(n) {
  if n == 0 {
    t = """
                        first line
                          two more spaces

                        last line
                        """;
    t
  } else { "none" }
}
main(m: MainArgs) {
  m.stdout <- poem(n: 0);
}
"#
    );
    // The program writes the same lines before and after formatting.
    for (name, text) in [("tls-deep-src", src), ("tls-deep-out", out.as_str())] {
        let o = run(name, text, "", &[]);
        assert_eq!(
            (o.status, o.stdout.as_str()),
            (0, "first line\n  two more spaces\n\nlast line\n"),
            "{name}: {}",
            o.stderr
        );
    }
}

/// The same string written at no indentation, so the formatter moves its statement right of
/// the string's lines; a closing delimiter indented by a tab; and a `"""` string whose opening
/// delimiter does not end its line, which is kept as written, spaces and all.
#[test]
fn a_triple_quoted_string_keeps_its_value_whatever_the_indentation() {
    let src = "f(n) {\nif n == 0 {\nt = \"\"\"\nleft\n  right\n\"\"\";\nt\n} else {\n\"\"\"a\n          b\"\"\"\n}\n}\n\ng() {\n  if true {\n    u = \"\"\"\n\tx\n\t  y\n\t\"\"\";\n    u\n  } else { \"\" }\n}\n";
    let out = fmt_strings(
        src.as_bytes(),
        &["left\n  right", "a\n          b", "x\n  y", ""],
    );
    assert_eq!(
        out,
        "f(n) {\n  if n == 0 {\n    t = \"\"\"\nleft\n  right\n\"\"\";\n    t\n  } else {\n    \"\"\"a\n          b\"\"\"\n  }\n}\n\ng() {\n  if true {\n    u = \"\"\"\n\tx\n\t  y\n\t\"\"\";\n    u\n  } else { \"\" }\n}\n"
    );
}

/// A line that begins inside a hole is not a line of the string, so it is not stripped and
/// may be indented less than the closing delimiter; the formatter keeps the hole as written,
/// and with it the string inside the hole.
#[test]
fn a_triple_quoted_string_with_a_hole_over_two_lines_keeps_its_value() {
    let src = "label(n) {\n      if n > 0 {\n            s = \"\"\"\n                total: ${add(n,\n  1, \"x\")}\n                end\n                \"\"\";\n            s\n      } else { \"\" }\n}\n";
    let out = fmt_strings(src.as_bytes(), &["total: ${}\nend", "x", ""]);
    assert_eq!(
        out,
        "label(n) {\n  if n > 0 {\n    s = \"\"\"\n                total: ${add(n,\n  1, \"x\")}\n                end\n                \"\"\";\n    s\n  } else { \"\" }\n}\n"
    );
}

/// A comment after the closing `"""` stays on its line, and `//` inside the string is text, not
/// a comment.
#[test]
fn a_comment_after_a_triple_quoted_string_stays_after_it() {
    let src = "f() {\n        if true {\n            t = \"\"\"\n              a // not a comment\n              \"\"\"; // why\n            t\n        } else { \"\" }\n}\n";
    let out = fmt_strings(src.as_bytes(), &["a // not a comment", ""]);
    assert_eq!(
        out,
        "f() {\n  if true {\n    t = \"\"\"\n              a // not a comment\n              \"\"\"; // why\n    t\n  } else { \"\" }\n}\n"
    );
}

/// Every escape DESIGN.md sec:lexical lists, `\n \t \r \0 \\ \" \$ \u{1F600}`, in a `"` string
/// and in a `"""` string two blocks deep, is written back byte for byte: as the escape, never
/// as the character it stands for, and `\u{…}` with its digits as spelled.
#[test]
fn every_escape_is_kept_byte_for_byte() {
    let escapes = [
        r"\n",
        r"\t",
        r"\r",
        r"\0",
        r"\\",
        r#"\""#,
        r"\$",
        r"\u{1F600}",
        r"\u{1f600}",
        r"\u{0000e9}",
        r"\u{0}",
    ];
    let chars = [
        "\n",
        "\t",
        "\r",
        "\0",
        "\\",
        "\"",
        "$",
        "\u{1F600}",
        "\u{1F600}",
        "\u{e9}",
        "\0",
    ];
    for (esc, c) in escapes.iter().zip(chars) {
        let one = format!("s=\"a{esc}b\";\n");
        let deep = format!(
            "f(n){{\n      if n==0 {{\n            t = \"\"\"\n              a{esc}b\n                {esc}\n              \"\"\";\n            t\n      }} else {{\"\"}}\n}}\n"
        );
        let want_one = format!("a{c}b");
        let want_deep = format!("a{c}b\n  {c}");
        let out = fmt_strings(one.as_bytes(), &[&want_one]);
        assert_eq!(out, format!("s = \"a{esc}b\";\n"), "{esc}");
        let out = fmt_strings(deep.as_bytes(), &[&want_deep, ""]);
        assert_eq!(
            out,
            format!(
                "f(n) {{\n  if n == 0 {{\n    t = \"\"\"\n              a{esc}b\n                {esc}\n              \"\"\";\n    t\n  }} else {{ \"\" }}\n}}\n"
            ),
            "{esc}"
        );
    }
    // `\$` before `{` is a dollar sign, not a hole, and `${` after `\\` is a hole.
    let src = "s = \"\\${x} \\\\${y}\";\n";
    let out = fmt_strings(src.as_bytes(), &["${x} \\${}"]);
    assert_eq!(out, src);
    // All of them in one string, side by side.
    let all: String = escapes.concat();
    let src = format!("s=\"{all}\";\n");
    let out = fmt_strings(src.as_bytes(), &[&chars.concat()]);
    assert_eq!(out, format!("s = \"{all}\";\n"));
}

/// Line ends. DESIGN.md sec:lexical: "Line endings normalize to `\n`: `\r\n` and a lone `\r`
/// are each one line break", so a file with `\r\n` or `\r` line ends is the same program as
/// with `\n`, and its `"""` strings hold `\n` between their lines. DESIGN says nothing of the
/// line ends the formatter writes; it writes `\n`, the normalized form, so formatting a CRLF
/// file gives the text that formatting its `\n` spelling gives. A `\r` written as an escape is
/// not a line end and stays an escape.
#[test]
fn a_crlf_source_formats_as_its_lf_spelling() {
    let lf = "// Lines of a poem.\npoem(n){\n        if n==0 {\n                    t = \"\"\"\n                        one\\r\n\n                          two\n                        \"\"\";\n                    t\n        } else {\"none\"}\n}\nmain(m: MainArgs) { m.stdout <- poem(n: 0); }\n";
    let want = ["one\r\n\n  two", "none"];
    let expected = fmt_strings(lf.as_bytes(), &want);
    assert!(expected.contains("one\\r\n"));
    let crlf = lf.replace('\n', "\r\n");
    let cr = lf.replace('\n', "\r");
    // Mixed: each line break written one of the three ways in turn. A `\r` written before a
    // `\n` would make one `\r\n` with it, so the turn puts no `\r` before an empty `\n` line.
    let mut mixed = String::new();
    for (i, line) in lf.split_inclusive('\n').enumerate() {
        mixed += &line.replace('\n', ["\n", "\r\n", "\r"][i % 3]);
    }
    for (name, src) in [("crlf", &crlf), ("cr", &cr), ("mixed", &mixed)] {
        let out = fmt_strings(src.as_bytes(), &want);
        assert_eq!(out, expected, "{name}");
        assert!(!out.contains('\r'), "{name}");
        let o = run(&format!("tls-{name}"), src, "", &[]);
        assert_eq!(
            (o.status, o.stdout.as_str()),
            (0, "one\r\n\n  two\n"),
            "{name}: {}",
            o.stderr
        );
    }
    // A `\r\n` right after the opening `"""` and right before the closing one is the line break
    // the stripping drops, as `\n` is.
    let src = "s = \"\"\"\r\n  a\r\n  \"\"\";\r\n";
    assert_eq!(
        fmt_strings(src.as_bytes(), &["a"]),
        "s = \"\"\"\n  a\n  \"\"\";\n"
    );
    // A carriage return inside a `"` string is a line break, which a `"` string may not hold, so
    // the file is rejected at the string, as one with `\n` there is.
    for src in ["s = \"a\rb\";\n", "s = \"a\r\nb\";\r\n", "s = \"a\nb\";\n"] {
        let e = format_source(src.as_bytes()).unwrap_err();
        assert!(
            e.starts_with("1:5: this `\"` string reaches the end of its line"),
            "{e}"
        );
    }
}
