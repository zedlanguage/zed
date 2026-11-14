//! The completeness pass over diagnostics (row TEST-complete-diagnostics): the cases
//! COMPLETENESS.md lists that the other files leave out. Expected results are from DESIGN.md
//! step L1.29 and its rows L1.29a, L1.29b and L1.29d.

use zedc::run::load;

use super::{rejected, steps};

/// The rendered errors of the bytes `src`, which do not load.
fn refused(src: &[u8]) -> String {
    match load(src) {
        Ok(_) => panic!("accepted"),
        Err(e) => e,
    }
}

#[test]
fn a_hidden_character_on_a_shown_line_is_escaped_and_underlines_count_its_escape() {
    // DESIGN L1.29: underlines are placed by terminal columns, a character printed escaped
    // taking the columns of its escape (`\u{1B}` six). The place in the headline and the
    // steps counts characters of the source, so `1` is at column 13.
    let out = refused(b"x = \"a\x1bb\" + 1;\n");
    let want = [
        "1:5: `+` does not take (\"a\\u{1B}b\", 1): no arrow of `+` takes these types.",
        "  [1] 1:5: this expression is \"a\\u{1B}b\"",
        "      1 | x = \"a\\u{1B}b\" + 1;",
        "        |     ^^^^^^^^^^ [1]",
        "        |     ^^^^^^^^^^^^^^ [3, 4, 5, 6]",
        "        |                  ^ [2]",
        "  [2] 1:13: this literal, 1, is 1",
    ];
    let got: Vec<&str> = out.lines().take(want.len()).collect();
    assert_eq!(got, want, "{out}");
    assert!(!out.contains('\x1b'), "{out:?}");
}

#[test]
fn two_diagnostics_each_show_their_own_line_with_its_escapes() {
    // Each source line is shown once over all the diagnostics; two lines, two quotes.
    let out = refused(b"x = \"\x1b\" + 1;\ny = \"\x1b\" + 2;\n");
    assert_eq!(
        out.matches("      1 | x = \"\\u{1B}\" + 1;").count(),
        1,
        "{out}"
    );
    assert_eq!(
        out.matches("      2 | y = \"\\u{1B}\" + 2;").count(),
        1,
        "{out}"
    );
    assert!(!out.contains("is shown above"), "{out}");
    assert!(!out.contains('\x1b'), "{out:?}");
}

#[test]
fn a_file_that_is_not_utf8_is_placed_at_its_first_bad_byte() {
    // The refusal of the source loader passes through the same report: its place, then why,
    // with no derivation.
    let out = refused(b"x = 1;\ny = \xff;\n");
    assert!(out.starts_with("2:5: "), "{out}");
    assert_eq!(out.lines().count(), 1, "{out}");
}

#[test]
fn a_step_that_repeats_an_earlier_one_is_shown_only_the_first_time() {
    // DESIGN L1.29: both calls of `f` derive from its declaration; the second call's chain
    // stops at its own step. The same for two uses of one name.
    let out = rejected("f(positional a) = a ++ \"!\";\ny = f(\"s\") + f(\"t\");\n");
    assert_eq!(
        steps(&out),
        [
            "this call of `f` gives String",
            "`f` is declared here with no type written for `a` or its result; the type the \
             checker found for `f` is `(String) -> String`",
            "this call of `f` gives String",
            "`+` takes (int, int) -> int",
            "`+` takes (f64, f64) -> f64",
            "`+` takes (rat, rat) -> rat",
            "`+` takes (f32, f32) -> f32",
        ],
        "{out}"
    );
    let out = rejected("s = \"a\";\ny = s + s;\n");
    assert_eq!(
        steps(&out)[..4],
        [
            "`s` is \"a\" here",
            "`s` is defined as this expression, \"a\"",
            "this expression is \"a\"",
            "`s` is \"a\" here",
        ],
        "{out}"
    );
}
