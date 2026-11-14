//! Step L1.29d: a syntax error and recovery from it. The message names the token the parse
//! stopped at, the tokens it expected there in the order of the grammar, and each bracket, block
//! or call still open, with its line and column. The parse resumes at the next line that starts
//! in the first column, so one file reports its syntax errors and its type errors together, each
//! once; a name that a broken declaration would define gets no row saying it is not defined, and
//! each repair offered parses.

use zedc::run::load;

use super::rejected;

/// The headline lines of the rendered diagnostics `out`: those that start with a line and
/// column, not the steps under them.
fn headlines(out: &str) -> Vec<&str> {
    out.lines()
        .filter(|l| {
            l.split(':')
                .next()
                .is_some_and(|n| n.parse::<usize>().is_ok())
        })
        .collect()
}

/// The repairs `out` offers: the code of each step that begins `repair: `.
fn repairs(out: &str) -> Vec<&str> {
    out.lines()
        .filter_map(|l| l.split_once(": repair: `")?.1.strip_suffix('`'))
        .collect()
}

/// `src` with the line holding `old` replaced by the repair `new`, the rewritten line.
fn repaired(src: &str, old: &str, new: &str) -> String {
    src.lines()
        .map(|l| if l == old { new } else { l })
        .map(|l| format!("{l}\n"))
        .collect()
}

/// Panics unless `src` with the line `old` replaced by each repair of `out` passes the parse.
fn each_repair_parses(src: &str, old: &str, out: &str) {
    let rs = repairs(out);
    assert!(!rs.is_empty(), "no repair:\n{out}");
    for r in rs {
        let fixed = repaired(src, old, r);
        let out = load(fixed.as_bytes()).err().unwrap_or_default();
        assert!(
            !out.contains("Syntax error"),
            "the repair `{r}` does not parse:\n{fixed}{out}"
        );
    }
}

const PERIMETER: &str = "perimeter(positional w, positional h) = 2 * (w + h\n\
                         area(positional w, positional h) = w * h;\n\
                         main(m: MainArgs) {\n  m.stdout <- \"${area(2, 3)}\";\n}\n";

#[test]
fn an_unclosed_parenthesis_is_reported_at_the_next_declaration_and_named() {
    let out = rejected(PERIMETER);
    assert_eq!(
        headlines(&out),
        ["2:1: Syntax error at `area`. Try \
          `perimeter(positional w, positional h) = 2 * (w + h);` instead."],
        "{out}"
    );
    assert!(
        out.contains("1:45: `(` opens here and is still open at `area`"),
        "{out}"
    );
    assert!(
        out.contains("1:1: the declaration of `perimeter` begins here"),
        "{out}"
    );
    each_repair_parses(
        PERIMETER,
        "perimeter(positional w, positional h) = 2 * (w + h",
        &out,
    );
}

const DOUBLE_STAR: &str = "area(positional w, positional h) = w * * h;\n\
                           main(m: MainArgs) {\n  m.stdout <- \"${area(2, 3)}\";\n}\n";

#[test]
fn a_second_operator_is_reported_with_the_expected_tokens_and_its_deletion() {
    let out = rejected(DOUBLE_STAR);
    assert_eq!(
        headlines(&out),
        ["1:40: Syntax error at `*`. Try \
          `area(positional w, positional h) = w * h;` instead."],
        "{out}"
    );
    // The expected tokens, in the order of the grammar: a value starts here.
    assert!(out.contains("expected "), "{out}");
    each_repair_parses(
        DOUBLE_STAR,
        "area(positional w, positional h) = w * * h;",
        &out,
    );
}

const FIVE_AND_THREE: &str = "double(positional x) = x * 2;\n\
                              half(positional x) = x / 2r;\n\
                              broken1(positional x) = x + ;\n\
                              sq(positional x) = x * x;\n\
                              broken2(positional x) = (x + 1;\n\
                              cube(positional x) = x * x * x;\n\
                              broken3 x = 1;\n\
                              wrong(positional x) = x ++ 1;\n\
                              main(m: MainArgs) {\n  \
                              m.stdout <- \"${double(2)} ${sq(3)} ${cube(2)} ${half(1)}\";\n}\n";

#[test]
fn three_broken_declarations_give_three_errors_and_the_sound_ones_are_checked() {
    let out = rejected(FIVE_AND_THREE);
    let heads = headlines(&out);
    let syntax: Vec<&&str> = heads
        .iter()
        .filter(|h| h.contains("Syntax error"))
        .collect();
    assert_eq!(syntax.len(), 3, "{out}");
    for (h, line) in syntax.iter().zip(["3:", "5:", "7:"]) {
        assert!(h.starts_with(line), "{out}");
    }
    // The type error of a sound declaration after the broken ones is reported with them, once.
    assert_eq!(heads.len(), 4, "{out}");
    assert!(heads[3].starts_with("8:"), "{out}");
}

const USES_BROKEN: &str = "f(positional x) = x + 1;\n\
                           g(positional x) = f(x) * 2 +;\n\
                           main(m: MainArgs) {\n  y = g(2);\n  m.stdout <- \"${y}\";\n}\n";

#[test]
fn a_use_of_a_name_a_broken_declaration_defines_is_not_reported_undefined() {
    let out = rejected(USES_BROKEN);
    assert_eq!(headlines(&out).len(), 1, "{out}");
    assert!(headlines(&out)[0].starts_with("2:"), "{out}");
    assert!(!out.contains("not defined"), "{out}");
}

const ON_THE_LAST_LINE: &str = "f(positional x) = x + 1;\nh(positional x) = x +";

#[test]
fn an_error_on_the_last_line_is_reported_at_the_end_of_the_text() {
    let out = rejected(ON_THE_LAST_LINE);
    let heads = headlines(&out);
    assert_eq!(heads.len(), 1, "{out}");
    assert!(
        heads[0].starts_with("2:22: Syntax error at the end of the text."),
        "{out}"
    );
}

const ONE_BROKEN_UNIT: &str = "f(positional x) = (x +\n";

#[test]
fn a_unit_that_is_one_broken_declaration_gives_one_error() {
    let out = rejected(ONE_BROKEN_UNIT);
    assert_eq!(headlines(&out).len(), 1, "{out}");
    assert!(out.contains("`(` opens here and is still open"), "{out}");
}

const EVERY_ONE_FAILS: &str = "a = (1 +;\nb = [2, ;\nc = 3 * * 4;\n";

#[test]
fn a_file_whose_every_declaration_fails_reports_each() {
    let out = rejected(EVERY_ONE_FAILS);
    let heads = headlines(&out);
    assert_eq!(heads.len(), 3, "{out}");
    for (h, line) in heads.iter().zip(["1:", "2:", "3:"]) {
        assert!(h.starts_with(line) && h.contains("Syntax error"), "{out}");
    }
}

const NESTED: &str = "main(m: MainArgs) {\n  a = [1, 2, (3 + 4];\n  m.stdout <- \"${a}\";\n}\n";

#[test]
fn an_error_inside_a_nested_construct_names_each_construct_open() {
    let out = rejected(NESTED);
    let heads = headlines(&out);
    assert_eq!(heads.len(), 1, "{out}");
    assert!(heads[0].starts_with("2:20: Syntax error at `]`."), "{out}");
    for open in [
        "2:14: `(` opens here",
        "2:7: `[` opens here",
        "1:19: `{` opens here",
    ] {
        assert!(out.contains(open), "{open}:\n{out}");
    }
}

const FIRST_LINE: &str = "f(positional x) = x + 1;\ng(x = 1;\nh(positional x) = x ++ 1;\n";

#[test]
fn an_error_on_the_first_line_of_a_declaration_and_a_type_error_after_it() {
    let out = rejected(FIRST_LINE);
    let heads = headlines(&out);
    assert_eq!(heads.len(), 2, "{out}");
    assert!(
        heads[0].starts_with("2:") && heads[0].contains("Syntax error"),
        "{out}"
    );
    assert!(
        heads[1].starts_with("3:") && !heads[1].contains("Syntax error"),
        "{out}"
    );
}

const CONTINUED: &str = "f(positional x) =\nx + 1;\nh(positional x) = x +* 1;\n\
                         main(m: MainArgs) {\n  m.stdout <- \"${f(1)}\";\n}\n";

#[test]
fn a_continuation_in_the_first_column_of_a_sound_declaration_is_part_of_it() {
    let out = rejected(CONTINUED);
    let heads = headlines(&out);
    assert_eq!(
        heads,
        ["3:22: Syntax error at `*`. Try `h(positional x) = x + 1;` instead."],
        "{out}"
    );
    each_repair_parses(CONTINUED, "h(positional x) = x +* 1;", &out);
}

const TWO_ON_A_LINE: &str = "x = 1; y = 2 +;\nz = y;\nw = 1 ++ 2;\n";

#[test]
fn declarations_that_fail_together_on_one_line_define_each_of_their_names() {
    let out = rejected(TWO_ON_A_LINE);
    let heads = headlines(&out);
    assert_eq!(heads.len(), 2, "{out}");
    assert!(heads[0].starts_with("1:15: Syntax error at `;`."), "{out}");
    assert!(heads[1].starts_with("3:"), "{out}");
    assert!(!out.contains("not defined"), "{out}");
}

/// A function whose block parses before a trailer that does not: the trailer's own message,
/// not an error at the trailer's first word.
const TRAILER: &str = "f(positional x) -> int { x } test { 1 with y = 0 -> 1 }\n\
                       g(positional x) = x ++ 1;\n";

#[test]
fn a_failing_trailer_after_a_block_is_reported_inside_it() {
    let out = rejected(TRAILER);
    let heads = headlines(&out);
    assert_eq!(heads.len(), 2, "{out}");
    assert!(
        heads[0].starts_with("1:39: The test case `1 with y = 0 -> 1` of `f`"),
        "{out}"
    );
    assert!(heads[1].starts_with("2:"), "{out}");
}

/// Checking one unit alone and after the others gives the same diagnostics.
#[test]
fn each_unit_gives_the_same_diagnostics_alone_and_in_a_batch() {
    let units = [
        PERIMETER,
        DOUBLE_STAR,
        FIVE_AND_THREE,
        USES_BROKEN,
        ON_THE_LAST_LINE,
        ONE_BROKEN_UNIT,
        EVERY_ONE_FAILS,
        NESTED,
        FIRST_LINE,
        CONTINUED,
        TWO_ON_A_LINE,
        TRAILER,
    ];
    let batch: Vec<String> = units.iter().map(|u| rejected(u)).collect();
    for (u, want) in units.iter().zip(&batch).rev() {
        let alone = std::thread::spawn({
            let u = u.to_string();
            move || load(u.as_bytes()).err().unwrap_or_default()
        })
        .join()
        .unwrap();
        assert_eq!(&alone, want);
    }
}

/// `n` declarations, each leaving a `(` open, each on a line of its own. No line holds a `=` or
/// `;`, so a parse restarted at a line reads to the end of the unit before it fails.
pub(super) fn left_open(n: usize) -> String {
    (0..n).map(|i| format!("(x{i} +\n")).collect()
}

/// `src`, [`left_open`] of `n`, gives one error for each of its `n` declarations.
pub(super) fn declarations_left_open_recovered(src: &str, n: usize) {
    let out = rejected(src);
    assert_eq!(headlines(&out).len(), n, "{out}");
}

/// 1, 2 and 9 declarations left open (`bench::syntax_recovery` times 200 and 1600).
#[test]
fn many_declarations_left_open() {
    for n in [1, 2, 9] {
        declarations_left_open_recovered(&left_open(n), n);
    }
}
