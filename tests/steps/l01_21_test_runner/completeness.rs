//! The completeness pass over the runner (row TEST-complete-diagnostics): the cases
//! COMPLETENESS.md lists that the other files leave out. Expected results are from DESIGN.md
//! step L1.21 and "The document is the first test suite" (sec:plan).

use zedc::rejection::Row;
use zedc::testing::command;

use super::checks;

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

/// The file `name` holding `text`, in a folder of this file's own, so no other test's files
/// meet it.
fn unit(name: &str, text: &str) -> String {
    let dir = std::env::temp_dir().join("zed-l01-21-completeness");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, text).unwrap();
    path.display().to_string()
}

#[test]
fn a_unit_the_parser_rejects_fails_on_its_syntax_error_alone() {
    // Its tables cannot be read, so no row is listed; the run still fails.
    let got = checks("f(x) = x + 1 test { 1 -> 2 }\ng = (;\n");
    assert_eq!(got.len(), 1, "{got:?}");
    assert!(got[0].starts_with("2:"), "{got:?}");
    assert!(!got[0].ends_with(": ok"), "{got:?}");
}

#[test]
fn a_rejected_unit_with_no_mark_fails_on_its_diagnostic_and_each_row() {
    let got = checks("f(x) = x + 1 test { 1 -> 2 }\ng = 3 + \"pounds\";\n");
    assert_eq!(got.len(), 2, "{got:?}");
    assert!(
        got.contains(&"1:21: `1 -> 2` of `f`: not run, since the unit is rejected".into()),
        "{got:?}"
    );
    assert!(
        got.iter()
            .any(|c| c.starts_with("2:") && !c.ends_with(": ok")),
        "{got:?}"
    );
}

#[test]
fn a_mark_in_an_accepted_unit_fails_and_its_rows_still_run() {
    let got = checks("f(x) = x + 1 test { 1 -> 2, 2 -> 4 }\ng = 1;  // ✗ Syntax error: none\n");
    assert_eq!(got.len(), 3, "{got:?}");
    assert!(
        got.contains(&"2:1: the line is marked ✗ and the unit is accepted".into()),
        "{got:?}"
    );
    assert!(got.contains(&"1:21: ok".into()), "{got:?}");
    assert!(
        got.contains(&"1:29: `2 -> 4` of `f`: the result is 3".into()),
        "{got:?}"
    );
}

#[test]
fn two_marked_lines_each_pass_on_their_own_diagnostic() {
    let src = "f(x) {\n  y = 1;\n  y = 2;  // ✗ Rebinding in the same scope: y = 1 above\n  \
               z = 1;\n  z = 2;  // ✗ Rebinding in the same scope: z = 1 above\n  y + z\n}\n";
    assert_eq!(checks(src), ["3:3: ok", "5:3: ok"]);
}

#[test]
fn a_mark_naming_no_row_fails_even_on_a_line_with_its_diagnostic() {
    let src = "f(x) {\n  y = 1;\n  y = 2;  // ✗ y is bound twice\n  y\n}\n";
    let got = checks(src);
    assert_eq!(got.len(), 1, "{got:?}");
    assert!(
        got[0].starts_with("3:3: the line is marked ✗ and its comment names no row"),
        "{got:?}"
    );
}

#[test]
fn a_row_named_with_a_parenthesis_in_its_code_is_named_whole() {
    // DESIGN: the comment begins with the row's first column "up to any parenthesis"; the
    // parentheses inside a code span of the name are part of it.
    let name = "Function without a cost claim in a unit under `@cost(#required);`";
    let row = Row::ALL.iter().copied().find(|r| r.name() == name);
    assert!(row.is_some(), "{name}");
    assert_eq!(Row::named_by(&format!(" {name}: f has none")), row);
    // Cut at the parenthesis, it names no row.
    assert_eq!(
        Row::named_by(" Function without a cost claim in a unit under `@cost: f"),
        None
    );
}

#[test]
fn a_comment_with_no_space_after_the_mark_names_its_row() {
    assert_eq!(
        Row::named_by("Rebinding in the same scope: y"),
        Some(Row::Rebinding)
    );
    assert_eq!(
        Row::named_by("\t Rebinding in the same scope: y"),
        Some(Row::Rebinding)
    );
    assert_eq!(Row::named_by(""), None);
    assert_eq!(Row::named_by(":"), None);
}

#[test]
fn every_row_is_named_by_its_own_name_and_a_colon() {
    for &r in Row::ALL {
        assert_eq!(
            Row::named_by(&format!(" {}: x", r.name())),
            Some(r),
            "{}",
            r.name()
        );
    }
}

#[test]
fn a_passing_and_a_failing_file_add_their_counts_and_fail_the_run() {
    let pass = unit("pass.zed", "double(positional x) = x * 2 test { 1 -> 2 }\n");
    let fail = unit("fail.zed", "double(positional x) = x * 2 test { 1 -> 3 }\n");
    let (status, out, err) = run(&[&pass, &fail]);
    assert_eq!(status, 1);
    assert_eq!(
        out,
        format!(
            "{fail}:1:37: `1 -> 3` of `double`: the result is 2\n\
             1 passed, 1 failed, 0 rejection units\n"
        )
    );
    assert_eq!(err, "");
}

#[test]
fn an_empty_file_has_no_test_and_fails() {
    let empty = unit("empty.zed", "");
    assert_eq!(
        run(&[&empty]),
        (
            1,
            format!(
                "{empty}: no test: the unit has no table row and no ✗ mark\n\
                 0 passed, 1 failed, 0 rejection units\n"
            ),
            String::new()
        )
    );
}

#[test]
fn a_file_of_comments_alone_has_no_test_and_fails() {
    // A ✗ on a line that is wholly a comment marks a variant, not a line: it is no test.
    let a = unit("comments.zed", "// x = 1;  ✗ Syntax error: a variant\n");
    let (status, out, _) = run(&[&a]);
    assert_eq!(status, 1, "{out}");
    assert!(out.starts_with(&format!("{a}: no test: ")), "{out}");
}

#[test]
fn a_file_that_cannot_be_read_after_one_that_passes_is_a_usage_error() {
    let pass = unit(
        "before.zed",
        "double(positional x) = x * 2 test { 1 -> 2 }\n",
    );
    let (status, _, err) = run(&[&pass, "/nonexistent/zed-l01-21-completeness.zed"]);
    assert_eq!(status, 2);
    assert!(
        err.starts_with("/nonexistent/zed-l01-21-completeness.zed: "),
        "{err}"
    );
}

#[test]
fn a_rejection_unit_counts_once_however_many_lines_it_marks() {
    let a = unit(
        "two-marks.zed",
        "f(x) {\n  y = 1;\n  y = 2;  // ✗ Rebinding in the same scope: y = 1 above\n  \
         z = 1;\n  z = 2;  // ✗ Rebinding in the same scope: z = 1 above\n  y + z\n}\n",
    );
    assert_eq!(
        run(&[&a]),
        (
            0,
            "2 passed, 0 failed, 1 rejection unit\n".into(),
            String::new()
        )
    );
}

#[test]
fn a_flag_with_no_value_is_a_usage_error_and_runs_nothing() {
    let pass = unit("flag.zed", "double(positional x) = x * 2 test { 1 -> 2 }\n");
    for flag in ["--target", "--option"] {
        let (status, out, err) = run(&[&pass, flag]);
        assert_eq!(status, 2, "{flag}");
        assert_eq!(out, "", "{flag}");
        assert!(
            err.starts_with(&format!("`{flag}` is the last word of the command line")),
            "{err}"
        );
    }
}

#[test]
fn an_unknown_target_is_a_usage_error() {
    let pass = unit(
        "target.zed",
        "double(positional x) = x * 2 test { 1 -> 2 }\n",
    );
    let (status, out, err) = run(&["--target", "nowhere", &pass]);
    assert_eq!((status, out.as_str()), (2, ""));
    assert!(
        err.starts_with("`--target nowhere`: `nowhere` is no target. Write one of "),
        "{err}"
    );
}

#[test]
fn no_file_is_a_usage_error() {
    let (status, out, err) = run(&[]);
    assert_eq!((status, out.as_str()), (2, ""));
    assert!(err.starts_with("usage: zedc test "), "{err}");
}

#[test]
fn a_known_target_runs_the_rows_for_it() {
    let pass = unit(
        "known-target.zed",
        "double(positional x) = x * 2 test { 1 -> 2 }\n",
    );
    for target in ["x86_64-linux", "aarch64-linux", "riscv64-linux"] {
        assert_eq!(
            run(&["--target", target, &pass]),
            (
                0,
                "1 passed, 0 failed, 0 rejection units\n".into(),
                String::new()
            ),
            "{target}"
        );
    }
}

#[test]
fn a_rejected_file_fails_its_rows_and_prints_its_diagnostic() {
    // The row cannot run and fails with its reason; the rejection fails too; neither is a
    // rejection unit, since no line is marked ✗.
    let rej = unit(
        "rejected.zed",
        "f(positional x) = x + 1 test { 1 -> 2 }\ng = 3 + \"pounds\";\n",
    );
    let (status, out, err) = run(&[&rej]);
    assert_eq!(status, 1, "{out}");
    assert_eq!(err, "");
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(
        lines[0],
        format!("{rej}:1:32: `1 -> 2` of `f`: not run, since the unit is rejected")
    );
    assert!(
        lines[1].starts_with(&format!("{rej}:2:5: `+` does not take (3, \"pounds\")")),
        "{out}"
    );
    assert_eq!(
        lines.last(),
        Some(&"0 passed, 2 failed, 0 rejection units"),
        "{out}"
    );
}
