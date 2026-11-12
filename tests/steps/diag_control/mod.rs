//! Plan row DIAG-control: a diagnostic printed to a terminal shows a character of the program's
//! text that a terminal would not show as itself (a control character, a format character such
//! as U+202E, a space other than U+0020) in Zed's escape form `\u{1B}`, in the message, in each
//! step, in the quoted source line and in a printed type, so an ESC[2J in a string, the unit's own
//! or a dependency's, cannot clear the reader's screen (DESIGN.md sec:diagnostics, "Characters a
//! terminal does not show"). A printed string type is a Zed literal that reads back as the same
//! type. The diagnostic itself keeps the text as it is: only its printing escapes.

use std::path::{Path, PathBuf};

use zed_kernel::Value;
use zed_tests::scaling;
use zedc::check::read::parse_type;
use zedc::check::ty::{Ty, printed};
use zedc::front::{Diagnostic, Quoted, Step, Unloaded};

const ESC: char = '\u{1B}';

/// The rendered diagnostics of the rejected program `src`.
fn rejected(src: &str) -> String {
    match zedc::run::load(src.as_bytes()) {
        Ok(_) => panic!("accepted:\n{src}"),
        Err(e) => e,
    }
}

/// Whether `out` holds a character a terminal acts on or does not show, other than the line
/// breaks of the layout.
fn raw(out: &str) -> Option<char> {
    out.chars()
        .find(|&c| c != '\n' && zedc::terminal::hidden(c))
}

#[test]
fn a_clear_screen_in_a_string_of_the_unit_prints_escaped() {
    let out = rejected("greet = \"\u{1B}[2J\" ++ 3;\nmain(m: MainArgs) = 0;\n");
    assert_eq!(raw(&out), None, "{out:?}");
    assert!(
        out.starts_with("1:9: `++` does not take (\"\\u{1B}[2J\", 3)"),
        "the headline's printed type: {out}"
    );
    assert!(
        out.contains("[1] 1:9: this expression is \"\\u{1B}[2J\""),
        "the step's printed type: {out}"
    );
    // The quoted line writes the ESC as its escape, and the marks stand under the literal as
    // printed: `"\u{1B}[2J"` is 11 columns, not the 6 characters of the source.
    assert!(
        out.contains("      1 | greet = \"\\u{1B}[2J\" ++ 3;\n        |         ^^^^^^^^^^^ [1]\n"),
        "the quoted line: {out}"
    );
}

#[test]
fn a_literal_written_with_an_escape_prints_as_written() {
    // Before, the printed type was Rust's form `"\u{1b}[2J"`, lower-case.
    let out = rejected("greet = \"\\u{1B}[2J\" ++ 3;\nmain(m: MainArgs) = 0;\n");
    assert!(
        out.starts_with("1:9: `++` does not take (\"\\u{1B}[2J\", 3)"),
        "{out}"
    );
    assert!(out.contains("1 | greet = \"\\u{1B}[2J\" ++ 3;"), "{out}");
}

#[test]
fn a_nul_a_delete_a_c1_control_and_a_bidi_override_print_escaped() {
    let out =
        rejected("greet = \"a\u{0}b\u{7F}c\u{9B}d\u{202E}e\" ++ 3;\nmain(m: MainArgs) = 0;\n");
    assert_eq!(raw(&out), None, "{out:?}");
    // A NUL is `\0` in a printed string, as Zed writes it; the quoted line gives every character
    // in the one form `\u{X}`.
    assert!(
        out.contains("this expression is \"a\\0b\\u{7F}c\\u{9B}d\\u{202E}e\""),
        "{out}"
    );
    assert!(
        out.contains("1 | greet = \"a\\u{0}b\\u{7F}c\\u{9B}d\\u{202E}e\" ++ 3;"),
        "{out}"
    );
}

#[test]
fn a_character_that_shows_is_left_alone() {
    // A multibyte letter, a wide character, an emoji, a combining mark on its letter (`q` has no
    // precomposed form with U+0301, so the source is NFC), a tab and a space: the quoted line
    // writes each as itself, the tab as four spaces. The printed type writes the tab as `\t` and
    // the mark, which a string value may hold with no letter before it, as `\u{301}`.
    let out = rejected("greet = \"é日😀q\u{301}\tx y\" ++ 3;\nmain(m: MainArgs) = 0;\n");
    assert_eq!(raw(&out), None, "{out:?}");
    assert!(
        out.contains("this expression is \"é日😀q\\u{301}\\tx y\""),
        "{out}"
    );
    assert!(
        out.contains("1 | greet = \"é日😀q\u{301}    x y\" ++ 3;"),
        "{out}"
    );
    // The literal is 1 + 1 + 2 + 2 + 1 + 4 + 3 + 1 = 15 columns: é, 日 and 😀 at their widths,
    // the mark at none.
    assert!(
        out.contains(&format!("\n        |         {} [1]\n", "^".repeat(15))),
        "{out}"
    );
}

/// A diagnostic placed at `col` with one step on the line `source`.
fn diagnostic(message: &str, source: &str, col: usize, width: usize) -> Diagnostic {
    Diagnostic {
        row: None,
        address: zedc::address::ContentAddress([0; 32]),
        line: 1,
        col,
        message: message.into(),
        steps: vec![Step {
            line: 1,
            col,
            text: format!("step {ESC}[2J"),
            source: source.into(),
            width,
        }],
        menu: format!("\n  1. repair {ESC}]0;title\u{7}"),
    }
}

#[test]
fn every_text_of_a_diagnostic_prints_escaped_and_the_diagnostic_keeps_its_text() {
    // A lone CR, which would return the terminal to the start of the line, and a NUL in the
    // quoted line; an ESC in the message, the step and the repair.
    let d = diagnostic(
        &format!("message {ESC}[2J"),
        "x = \"a\rb\u{0}c\" ++ y;",
        13,
        1,
    );
    let shown = d.to_string();
    // The `+` at character 13 stands at column 20 of the line as shown, after the 5 columns of
    // `\u{D}` and the 5 of `\u{0}`.
    assert_eq!(
        shown,
        format!(
            "1:13: message \\u{{1B}}[2J
  [1] 1:13: step \\u{{1B}}[2J
      1 | x = \"a\\u{{D}}b\\u{{0}}c\" ++ y;
        | {}^
  1. repair \\u{{1B}}]0;title\\u{{7}}",
            " ".repeat(20)
        )
    );
    assert_eq!(Quoted::default().show(&d), shown);
    // Printing changes nothing the diagnostic holds: a program given it reads the text as the
    // source has it.
    assert_eq!(d.message, format!("message {ESC}[2J"));
    assert_eq!(&*d.steps[0].source, "x = \"a\rb\u{0}c\" ++ y;");
    assert_eq!(d.steps[0].text, format!("step {ESC}[2J"));
}

#[test]
fn a_mark_after_an_escape_stands_under_its_character() {
    // `y` is character 16 of the line, shown after the escapes of the CR and the NUL.
    let d = diagnostic("m", "x = \"a\rb\u{0}c\" ++ y;", 16, 1);
    let out = d.to_string();
    let lines: Vec<&str> = out.lines().collect();
    let at = |l: &str, s: &str| l.find(s).expect(s);
    assert_eq!(at(lines[2], "y;"), at(lines[3], "^"), "{out}");
}

#[test]
fn a_refused_file_prints_escaped() {
    let why = Unloaded::Refused(format!("refused {ESC}[2J"));
    assert_eq!(
        why.report(Some("f.zed"), |_| String::new()),
        "f.zed:refused \\u{1B}[2J"
    );
}

#[test]
fn a_parse_error_keeps_the_raw_line_and_prints_it_escaped() {
    let src = format!("x = \"{ESC}[2J\" +;\n");
    let Err(why) = zedc::format::formatted(src.as_bytes()) else {
        panic!("accepted")
    };
    let Unloaded::Rejected(ds) = &why else {
        panic!("refused")
    };
    assert!(
        ds.iter()
            .flat_map(|d| &d.steps)
            .any(|s| s.source.contains(ESC)),
        "a step holds the line as written"
    );
    let out = why.report(None, |_| String::new());
    assert_eq!(raw(&out), None, "{out:?}");
    assert!(out.contains("x = \"\\u{1B}[2J\" +;"), "{out}");
}

/// The string types printed while checking `src`, each with its text.
fn printed_strings(src: &str) -> Vec<(Ty, String)> {
    printed::start();
    let _ = zedc::run::load(src.as_bytes());
    printed::take()
        .into_iter()
        .filter(|(_, text)| text.starts_with('"'))
        .collect()
}

#[test]
fn a_printed_string_type_reads_back_as_itself() {
    // An ESC, a NUL, a lone CR, a quote, a backslash, a `$` before `{`, which in a string starts
    // a hole, a `$` before anything else, a `'`, a non-breaking space and a letter that shows.
    let src =
        "greet = \"\u{1B}[2J\u{0}\\r\\\"\\\\\\${b}$x'\u{A0}é\" ++ 3;\nmain(m: MainArgs) = 0;\n";
    let seen = printed_strings(src);
    assert!(!seen.is_empty(), "the check printed no string type");
    for (t, text) in seen {
        assert_eq!(
            text, "\"\\u{1B}[2J\\0\\r\\\"\\\\\\${b}$x'\\u{A0}é\"",
            "the printed form"
        );
        assert_eq!(
            parse_type(&text),
            Ok(t),
            "`{text}` reads back as another type"
        );
    }
    // The text value prints the same way, and reads back to the value.
    let s = "\u{1B}\u{0}\r\n\t\"\\${$'\u{200B}\u{FDD5}é";
    let t = Ty::lit(&Value::str(s));
    let text = t.to_string();
    assert_eq!(
        text,
        "\"\\u{1B}\\0\\r\\n\\t\\\"\\\\\\${$'\\u{200B}\\u{FDD5}é\""
    );
    assert_eq!(parse_type(&text), Ok(t));
}

/// A package `name` of the files `files`, under the tests' directory for temporary files.
fn package_dir(name: &str, files: &[(&str, &str)]) -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("diag_control")
        .join(name);
    for (file, text) in files {
        let path = d.join(file);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }
    d
}

/// Runs `zedc run <file>` and gives its standard error.
fn run(file: &Path) -> String {
    let (mut out, mut err) = (Vec::new(), Vec::new());
    zedc::run::command(
        &["run", file.to_str().unwrap()],
        &mut "".as_bytes(),
        &mut out,
        &mut err,
    );
    String::from_utf8(err).unwrap()
}

#[test]
fn a_clear_screen_in_a_dependency_prints_escaped() {
    // A name an import brings in is not tied to its definition yet, so a string of the
    // dependency reaches a diagnostic through the dependency's own rejection.
    let d = package_dir(
        "unparsed",
        &[
            ("zed.manifest", "// the shop\n"),
            ("app/main.zed", "import pricing;\nmain(m: MainArgs) {}\n"),
            ("pricing.zed", "banner = \"\u{1B}[2J\" +;\n"),
        ],
    );
    let err = run(&d.join("app/main.zed"));
    assert_eq!(raw(&err), None, "{err:?}");
    assert!(
        err.contains("1 | banner = \"\\u{1B}[2J\" +;"),
        "the dependency's line: {err}"
    );
}

/// A line holding a string of about `n` bytes, one in eight an ESC.
fn long_line(n: usize) -> String {
    let body: String = (0..n / 8).map(|_| "\u{1B}[2Jabcd").collect();
    format!("x = \"{body}\" ++ y;")
}

#[test]
fn printing_a_quoted_string_scales() {
    let inputs = scaling::inputs(4000, |n| {
        let line = long_line(n);
        let col = line.chars().count() - 1;
        let d = diagnostic(&format!("message {}", &line[4..]), &line, col, 1);
        let t = Ty::lit(&Value::str(&line[5..line.len() - 8]));
        (d, t)
    });
    scaling::check_order("a diagnostic quoting a string of n bytes", 4000, 1, |n| {
        let (d, t) = &inputs[&n];
        let out = d.to_string();
        assert!(!out.contains(ESC));
        assert!(!t.to_string().contains(ESC));
    });
}
