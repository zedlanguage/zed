//! Completeness cases for step L25.8 (author P189): each operator `zedc test --mutate`
//! replaces, each form of an integer constant, each place in a definition a mutant can sit, and
//! each way a run of the command meets a file. DESIGN.md L25.8: "replaces one operator node at a
//! time (`<=` with `<`, `+` with `-`, a constant with its neighbor), skips each mutant the
//! optimizer proves equal to the original, runs the `test { }` tables against the rest, and
//! reports each mutant no table detects". The list of cases is COMPLETENESS.md.

use zedc::mutate::{self, Verdict};
use zedc::query::Db;
use zedc::testing::command;

use super::report;

/// Each mutant of `text` as `line:col: \`was\` replaced by \`to\` in \`name\` at path`, in
/// the order the run reports them, whatever its verdict.
pub(super) fn changes(text: &str) -> Vec<String> {
    let mut db = Db::new();
    let front = db.front(text);
    let (stmts, unit, _) = front.as_ref().as_ref().expect("the unit compiles");
    let found = mutate::mutants(text, stmts, unit).expect("the mutants are made");
    found
        .iter()
        .map(|m| {
            let line = mutate::describe(text, &unit.defs[m.def].name, m, &Verdict::Skipped)
                .expect("a skipped mutant is described");
            let line = line.replacen("skipped: ", "", 1);
            line.trim_end_matches(": the build stage gives the definition the original's term")
                .to_string()
        })
        .collect()
}

/// The `was` and `to` of each mutant of `text`.
fn pairs(text: &str) -> Vec<(String, String)> {
    changes(text)
        .iter()
        .map(|l| {
            let mut parts = l.split('`');
            let was = parts.nth(1).unwrap().to_string();
            let to = parts.nth(1).unwrap().to_string();
            (was, to)
        })
        .collect()
}

fn owned(list: &[(&str, &str)]) -> Vec<(String, String)> {
    list.iter()
        .map(|(a, b)| (a.to_string(), b.to_string()))
        .collect()
}

/// DESIGN: "`<=` with `<`". Each comparison is replaced by the one that differs from it only
/// at the boundary, and `==` and `!=` by each other; the mutant sits at the operator. On `int`
/// operands with no literal, each ordering also has its right operand moved by one across the
/// boundary (MUTATION.md H2), reported at the operator too.
#[test]
fn each_comparison_is_replaced_by_its_boundary_neighbor() {
    for (op, to, shifted) in [
        ("<", "<=", Some("a < b - 1")),
        ("<=", "<", Some("a <= b + 1")),
        (">", ">=", Some("a > b + 1")),
        (">=", ">", Some("a >= b - 1")),
        ("==", "!=", None),
        ("!=", "==", None),
    ] {
        let text = format!("f(positional a: int, b: int) = a {op} b test {{ (1, 2) -> true }}\n");
        let mut expected = vec![format!("1:34: `{op}` replaced by `{to}` in `f` at .0")];
        if let Some(s) = shifted {
            expected.push(format!("1:34: `a {op} b` replaced by `{s}` in `f` at .0"));
        }
        assert_eq!(changes(&text), expected, "{text}");
    }
}

/// DESIGN: "`+` with `-`", and `-` with `+` the same way. A sum at the root of an arithmetic
/// expression is also negated whole (H6), and a difference has its operands swapped (H11); a
/// difference is not negated, since `-(a - b)` is `b - a`.
#[test]
fn addition_and_subtraction_are_replaced_by_each_other() {
    for (op, to, other) in [("+", "-", "-(a + b)"), ("-", "+", "b - a")] {
        let text = format!("f(positional a: int, b: int) = a {op} b test {{ (1, 2) -> 3 }}\n");
        assert_eq!(
            changes(&text),
            [
                format!("1:34: `{op}` replaced by `{to}` in `f` at .0"),
                format!("1:34: `a {op} b` replaced by `{other}` in `f` at .0"),
            ],
            "{text}"
        );
    }
}

/// A product becomes a quotient only on a carrier where `/` is defined on the same operands
/// and gives the same carrier (rat and f64); a quotient becomes a product on both, and has its
/// operands swapped (H11). Each, at the root, is also negated whole (H6), on `int` too.
#[test]
fn multiplication_and_division_are_replaced_on_rat_and_f64() {
    for carrier in ["rat", "f64"] {
        let text =
            format!("f(positional a: {carrier}, b: {carrier}) = a * b test {{ (1, 2) -> 2 }}\n");
        assert_eq!(
            pairs(&text),
            owned(&[("*", "/"), ("a * b", "-(a * b)")]),
            "{text}"
        );
        let text =
            format!("f(positional a: {carrier}, b: {carrier}) = a / b test {{ (1, 2) -> 2 }}\n");
        assert_eq!(
            pairs(&text),
            owned(&[("/", "*"), ("a / b", "b / a"), ("a / b", "-(a / b)")]),
            "{text}"
        );
    }
    let text = "f(positional a: int, b: int) = a * b test { (1, 2) -> 2 }\n";
    assert_eq!(pairs(text), owned(&[("a * b", "-(a * b)")]), "{text}");
}

/// DESIGN: "a constant with its neighbor": an integer constant `n` gives `n - 1` and then
/// `n + 1`, written in decimal whatever form the source used. An integer literal has no sign
/// (sec:grammar `Integer`), so `-3` is `-` applied to the constant 3, whose neighbors 2 and 4
/// give -2 and -4; a constant beyond `i64` keeps its exact neighbors.
#[test]
fn each_form_of_an_integer_constant_gives_its_two_neighbors() {
    for (lit, below, above) in [
        ("7", "6", "8"),
        ("0", "-1", "1"),
        ("0x10", "15", "17"),
        ("1_000", "999", "1001"),
        (
            "9223372036854775807",
            "9223372036854775806",
            "9223372036854775808",
        ),
        (
            "100000000000000000000",
            "99999999999999999999",
            "100000000000000000001",
        ),
    ] {
        let text = format!("f(positional a: int) = a == {lit} test {{ 1 -> false }}\n");
        assert_eq!(
            pairs(&text),
            owned(&[
                ("==", "!="),
                (lit_shown(lit), below),
                (lit_shown(lit), above)
            ]),
            "{text}"
        );
    }
    let text = "f(positional a: int) = a == -3 test { 1 -> false }\n";
    assert_eq!(
        pairs(text),
        owned(&[("==", "!="), ("3", "2"), ("3", "4")]),
        "{text}"
    );
}

/// The text a report gives for the literal `lit`: its value in decimal.
fn lit_shown(lit: &str) -> &str {
    match lit {
        "0x10" => "16",
        "1_000" => "1000",
        _ => lit,
    }
}

/// A whole-number constant that takes `f64` from its use has its neighbors at `f64`: with
/// `+` replaced and the sum negated (H6), four mutants.
#[test]
fn a_whole_number_on_f64_has_its_neighbors_at_f64() {
    let text = "f(positional a: f64) = a + 2 test { 1.0 -> 3.0 }\n";
    assert_eq!(
        report(text),
        ["4 mutants: 4 detected, 0 undetected, 0 skipped, 0 not run"]
    );
    assert_eq!(pairs(text).len(), 4, "{text}");
}

/// Plan row TESTS-L25.8-neighbors: a literal passed to a parameter of a narrower type keeps
/// only the neighbors that type holds, since a value outside a declared range is a program the
/// checker rejects (MUTATION.md 3.7). `255` passed as a `u8` gives `254` and not `256`, by
/// position and by name; `-10` passed as an `int[-10..=0]` gives `-9` (the constant `10`
/// replaced by `9`) and not `-11`; the same literals at an `int` parameter keep both.
#[test]
fn a_literal_argument_keeps_the_neighbors_its_parameter_holds() {
    let cases = [
        (
            "g(positional x: u8) = x",
            "g(255)",
            ("255", "254"),
            ("255", "256"),
        ),
        ("g(x: u8) = x", "g(x: 255)", ("255", "254"), ("255", "256")),
        ("g(positional x: u8) = x", "g(0)", ("0", "1"), ("0", "-1")),
        (
            "g(positional x: int[-10..=0]) = x",
            "g(-10)",
            ("10", "9"),
            ("10", "11"),
        ),
    ];
    for (g, call, kept, dropped) in cases {
        let text = format!("{g}\nf(positional a: int) = a + {call} test {{ 0 -> 0 }}\n");
        let found = pairs(&text);
        let kept = (kept.0.to_string(), kept.1.to_string());
        let dropped = (dropped.0.to_string(), dropped.1.to_string());
        assert!(found.contains(&kept), "{text}: {found:?}");
        assert!(!found.contains(&dropped), "{text}: {found:?}");
    }
    let text = "g(positional x: int) = x\nf(positional a: int) = a + g(255) test { 0 -> 255 }\n";
    let found = pairs(text);
    for to in ["254", "256"] {
        let pair = ("255".to_string(), to.to_string());
        assert!(found.contains(&pair), "{text}: {found:?}");
    }
}

/// Plan row TESTS-L25.8-neighbors: the `==` to `!=` mutant, and the `!=` to `==` one, are
/// detected by a table whose row the comparison decides.
#[test]
fn an_equality_mutant_is_detected() {
    for op in ["==", "!="] {
        let text = format!(
            "f(positional a: int, b: int) = a {op} b test {{ (1, 1) -> {} }}\n",
            op == "=="
        );
        assert_eq!(
            report(&text),
            ["1 mutants: 1 detected, 0 undetected, 0 skipped, 0 not run"],
            "{text}"
        );
    }
}

/// Plan row TESTS-L25.8-neighbors: at `f64`, a literal at 2^53 has a neighbor above that
/// rounds back to 2^53 (2^53 + 1 is no `f64`; ties to even give 2^53), written as a decimal
/// and as an integer. That neighbor is the original program, so it is skipped, never reported
/// as a mutant no table detects; the neighbor below, 2^53 - 1, is an `f64` and is detected.
#[test]
fn an_f64_literal_at_two_to_the_53_gives_no_mutant_equal_to_the_original() {
    for lit in ["9007199254740992.0", "9007199254740992"] {
        let text =
            format!("f(positional x: f64) = x + {lit} test {{ 0.0 -> 9007199254740992.0 }}\n");
        let lines = report(&text);
        let counts = lines.last().expect("the counts");
        assert!(counts.contains(" 0 undetected,"), "{text}: {lines:?}");
        let skipped = (lines.iter()).filter(|l| l.contains("skipped:")).count();
        assert_eq!(skipped, 1, "{text}: {lines:?}");
    }
}

/// The column of an operator mutant is the operator's, after parentheses, line breaks and a
/// `//` comment between it and its left operand; so is that of a mutant of the whole operation
/// (H11, H6), whose operands keep the text the source gives them.
#[test]
fn the_operator_is_found_after_parentheses_and_a_comment() {
    assert_eq!(
        changes("f(positional a: int, b: int) = ((a)) - ((b)) test { (5, 2) -> 3 }\n"),
        [
            "1:38: `-` replaced by `+` in `f` at .0",
            "1:38: `((a)) - ((b))` replaced by `((b)) - ((a))` in `f` at .0",
        ]
    );
    assert_eq!(
        changes("f(positional a: int, b: int) = (a) // first\n  + (b) test { (1, 2) -> 3 }\n"),
        [
            "2:3: `+` replaced by `-` in `f` at .0",
            "2:3: `(a) + (b)` replaced by `-((a) + (b))` in `f` at .0",
        ]
    );
    assert_eq!(
        changes("f(positional a: int, b: int) = a /* x */ + b test { (1, 2) -> 3 }\n"),
        [
            "1:42: `+` replaced by `-` in `f` at .0",
            "1:42: `a + b` replaced by `-(a + b)` in `f` at .0",
        ]
    );
}

/// A mutant can sit anywhere in a definition's body: in a local binding, a tuple, a call's
/// argument, a string's interpolation, either branch of an `if` and its condition. Each is
/// detected by a row that reaches it.
#[test]
fn a_mutant_in_each_place_of_a_body_is_detected_by_a_row_that_reaches_it() {
    for text in [
        "f(positional a: int) {\n  b = a + 1;\n  return b * 2;\n} test { 1 -> 4 }\n",
        "f(positional a: int) = (a + 1, a - 1) test { 5 -> (6, 4) }\n",
        "g(positional a: int) = a;\nf(positional a: int) = g(a + 1) test { 1 -> 2 }\n",
        "f(positional a: int) = \"${a + 1}\" test { 1 -> \"2\" }\n",
        "f(positional a: int) = if a > 0 { a + 1 } else { a - 1 } test { 0 -> -1, 1 -> 2, 2 -> 3 }\n",
    ] {
        let lines = report(text);
        assert_eq!(lines.len(), 1, "{text}: {lines:?}");
        assert!(
            lines[0].contains(" 0 undetected, 0 skipped, 0 not run"),
            "{text}: {lines:?}"
        );
    }
}

/// A function with no table of its own is reached through the table of a function that calls
/// it, so its mutants are detected there: four in `g` (`+`, the negated sum, the constant 1's
/// two), and three in `f` (the negated product and the constant 2's two; a product of `int`
/// values has no `/` mutant).
#[test]
fn a_callee_s_mutants_are_detected_by_its_caller_s_table() {
    let text = "g(positional a: int) = a + 1;\nf(positional a: int) = g(a) * 2 test { 1 -> 4 }\n";
    assert_eq!(
        report(text),
        ["7 mutants: 7 detected, 0 undetected, 0 skipped, 0 not run"]
    );
}

/// Each row that reaches a mutant runs until one fails: a mutant the first row passes and the
/// second fails (`<=`) is detected, and one every row passes is reported with the rows
/// passing. The constant's neighbor 11 is left out, since on `int` `a < 11` is the `<=` mutant
/// again (H4).
#[test]
fn a_mutant_is_detected_by_any_row_and_undetected_only_when_every_row_passes() {
    assert_eq!(
        report("f(positional a: int) = a < 10 test { 0 -> true, 10 -> false }\n"),
        [
            "1:28: undetected: `10` replaced by `9` in `f` at .0.1: every row that reaches it \
             passes",
            "2 mutants: 1 detected, 1 undetected, 0 skipped, 0 not run",
        ]
    );
}

/// A definition with no operator and no integer constant has no mutant, and the report says
/// so by its count.
#[test]
fn a_definition_with_nothing_to_replace_has_no_mutant() {
    assert_eq!(
        report("f(positional a: int) = a test { 1 -> 1 }\n"),
        ["0 mutants: 0 detected, 0 undetected, 0 skipped, 0 not run"]
    );
}

fn run(args: &[&str]) -> (u8, String, String) {
    let args: Vec<String> = args.iter().map(|a| a.to_string()).collect();
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = command(&args, &mut out, &mut err);
    (
        status,
        String::from_utf8(out).unwrap(),
        String::from_utf8(err).unwrap(),
    )
}

fn unit(name: &str, text: &str) -> String {
    let path = zed_tests::step_helpers::scratch(format!("l25_08_cases/{name}"));
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(&path, text).unwrap();
    path.display().to_string()
}

/// A file with no row and no ✗ mark fails `zedc test` (step L1.21), so no mutant runs.
#[test]
fn a_file_with_no_test_runs_no_mutant() {
    let a = unit("none.zed", "f(positional a: int) = a + 1;\n");
    let (status, out, _) = run(&["--mutate", &a]);
    assert_eq!(status, 1);
    assert_eq!(
        out,
        format!(
            "{a}: no test: the unit has no table row and no ✗ mark\n\
             0 passed, 1 failed, 0 rejection units\n\
             no mutant runs: the original's checks fail\n"
        )
    );
}

/// A rejection unit, whose ✗ marks name the errors it must give, has no program to mutate; a
/// run with it and a unit with tables reports the mutants of the second alone.
#[test]
fn a_rejection_unit_adds_no_mutant() {
    let a = unit(
        "rejected.zed",
        "c0 = 1;\nc0 = 2;    // ✗ Rebinding in the same scope: c0 is bound above\n",
    );
    let b = unit(
        "plain.zed",
        "f(positional a: int) = a - 1 test { 3 -> 2 }\n",
    );
    let (status, out, _) = run(&["--mutate", &a, &b]);
    assert_eq!(status, 0, "{out}");
    assert!(
        out.ends_with("4 mutants: 4 detected, 0 undetected, 0 skipped, 0 not run\n"),
        "{out}"
    );
    assert!(out.contains(" 1 rejection unit\n"), "{out}");
}

/// The flags of `zedc test` follow `--mutate`: a target and the build's options are read as
/// for `zedc test`, and an option the build does not hold is a usage error.
#[test]
fn the_flags_of_zedc_test_follow_mutate() {
    let a = unit(
        "flags.zed",
        "f(positional a: int) = a - 1 test { 3 -> 2 }\n",
    );
    let (status, out, err) = run(&["--mutate", "--target", "x86_64-linux", &a]);
    assert_eq!((status, err.as_str()), (0, ""), "{out}");
    assert!(out.ends_with("4 mutants: 4 detected, 0 undetected, 0 skipped, 0 not run\n"));
    let (status, out, _) = run(&["--mutate", "--option", "noSuchOption", &a]);
    assert_eq!(status, 2, "{out}");
}
