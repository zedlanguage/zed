//! Rows of `test { }` tables: a function's, and `main`'s, each a wave.

use super::checks;

#[test]
fn a_wrong_row_reports_the_result() {
    let src = "square(positional x) = x * x test { 3 -> 9, 4 -> 15 }\n";
    assert_eq!(
        checks(src),
        ["1:37: ok", "1:45: `4 -> 15` of `square`: the result is 16"]
    );
}

#[test]
fn a_row_of_several_arguments_and_a_failure_value() {
    let src = "area(w, h) = w * h test { (2, 3) -> 6, (2, 3) -> 7 }\n\
               parse(positional s) = int(s) test { \"12\" -> 12, \"1.5\" -> #invalid }\n";
    assert_eq!(
        checks(src),
        [
            "1:27: ok",
            "1:40: `(2, 3) -> 7` of `area`: the result is 6",
            "2:37: ok",
            "2:49: ok",
        ]
    );
}

#[test]
fn a_row_that_stops_the_evaluator_fails() {
    // The checker passes every row a program it accepts can run; a string too long for its
    // length still stops it.
    let src = format!(
        "{}big(positional n: int) = len({}) * n test {{ 1 -> 1 }}\n",
        zed_tests::TWICE,
        zed_tests::too_long()
    );
    let got = checks(&src);
    assert_eq!(got.len(), 1);
    assert!(got[0].starts_with("2:494: `1 -> 1` of `big`: "), "{got:?}");
    assert!(!got[0].ends_with(": ok"), "{got:?}");
}

#[test]
fn a_main_row_compares_the_bytes_each_port_writes() {
    let src = "main(m: MainArgs) {\n  m.stdout <- upper(m.stdin[0] else #ioError -> \"\" else #outOfBounds -> \"\");\n}\n\
               test { \"abc\\n\" -> \"ABC\\n\", \"abc\" -> \"ABC\" }\n";
    assert_eq!(
        checks(src),
        [
            "4:8: ok",
            "4:28: `\"abc\" -> \"ABC\"` of `main`: `m.stdout` writes \"ABC\\n\"",
        ]
    );
}

#[test]
fn a_port_not_pushed_writes_nothing() {
    let src = "main(m: MainArgs) {\n  \
               m.stdout <- m.stdin[0] else #ioError -> \"\" else #outOfBounds -> \"\";\n}\n\
               test { \"a\" -> { stdout: \"a\\n\", stderr: \"\" }, \
               \"a\" -> { stdout: \"a\\n\", stderr: \"warning\\n\" } }\n";
    assert_eq!(
        checks(src),
        [
            "4:8: ok",
            "4:46: `\"a\" -> { stdout: \"a\\n\", stderr: \"warning\\n\" }` of `main`: `m.stderr` \
             writes \"\"",
        ]
    );
}

#[test]
fn a_files_port_is_given_as_a_function_of_the_path() {
    let src = "main(m: MainArgs) {\n  fs = main::files;\n  \
               m.stdout <- (fs[\"a.txt\"] else #ioError -> \"\" else #notFound -> \"\") ++ (fs[\"b.txt\"] else #ioError -> \"\" else #notFound -> \"\");\n}\n\
               test { { files: (p -> if p == \"a.txt\" { \"1\" } else { \"2\" }) } -> \"12\\n\" }\n";
    assert_eq!(checks(src), ["5:8: ok"]);
}

#[test]
fn a_row_of_the_wrong_shape_says_what_a_port_takes() {
    let src = "main(m: MainArgs) {\n  \
               m.stdout <- \"x\";\n  m.stderr <- \"y\";\n}\n\
               test { \"\" -> \"x\\n\", \"\" -> { stdout: \"x\\n\", stderr: 2 } }\n";
    assert_eq!(
        checks(src),
        [
            "5:8: ok",
            "5:21: `\"\" -> { stdout: \"x\\n\", stderr: 2 }` of `main`: the expected value of \
             `m.stderr` is a String, not 2",
        ]
    );
    // A standard input that is no String is refused when the unit is checked (plan row
    // PORT-main-key-values-unchecked); until then `3 -> …` failed only its own row, with "the
    // `Lines` port `m.stdin` is given as a String, not 3".
    let src = src.replace(
        "test { ",
        "test { 3 -> { stdout: \"x\\n\", stderr: \"y\\n\" }, ",
    );
    let got = checks(&src);
    assert_eq!(got.len(), 4, "{got:?}");
    assert!(got[0].contains("`main::stdin` does not take 3"), "{got:?}");
}

#[test]
fn a_wave_that_aborts_fails_its_row() {
    // A string too long for its length stops the wave.
    let src = format!(
        "{}main(m: MainArgs) {{\n  m.stdout <- {};\n}}\n\
         test {{ \"7\" -> \"7\\n\" }}\n",
        zed_tests::TWICE,
        zed_tests::too_long()
    );
    let got = checks(&src);
    assert_eq!(got.len(), 1);
    assert!(
        got[0].starts_with("5:8: `\"7\" -> \"7\\n\"` of `main`: "),
        "{got:?}"
    );
    assert!(
        got[0].contains("String too long: `++` would join"),
        "{got:?}"
    );
}

#[test]
fn a_main_with_a_wrong_header_reports_once_and_runs_no_row() {
    let src = "main(n: int) {\n  m.stdout <- \"x\";\n}\n\
               test { 1 -> \"x\\n\" }\n";
    // One error: its headline, then the notes of what `main` takes.
    let got = checks(src);
    assert_eq!(got.len(), 1, "{got:?}");
    assert_eq!(
        got[0].lines().next(),
        Some(format!("1:6: {}", zed_tests::main_param_message("n", "int")).as_str())
    );
}

#[test]
fn a_main_row_may_give_the_exit_status() {
    // The field `status` of the value is the status the run exits with, from 0 to 255.
    let src = "main(m: MainArgs) -> int {\n  m.stdout <- \"x\";\n  \
               if (m.stdin[0] else #ioError -> \"\" else #outOfBounds -> \"\") == \"no\" { 3 } else { 0 }\n}\n\
               test { \"no\" -> { stdout: \"x\\n\", status: 3 }, \"yes\" -> { stdout: \"x\\n\", status: 3 }, \
               \"no\" -> { stdout: \"x\\n\", status: 255 } }\n";
    assert_eq!(
        checks(src),
        [
            "5:8: ok",
            "5:46: `\"yes\" -> { stdout: \"x\\n\", status: 3 }` of `main`: the run exits with \
             status 0",
            "5:85: `\"no\" -> { stdout: \"x\\n\", status: 255 }` of `main`: the run exits with \
             status 3",
        ]
    );
}

#[test]
fn a_main_row_expecting_a_status_past_255_is_rejected_before_it_runs() {
    // DESIGN.md: the `status` of a row of `main` is an `int[0..=255]`, the range of `main`'s
    // result, so a row expecting a status outside it is rejected at compile time (step
    // L1.19), whether the status is written as a literal or computed.
    for (status, col) in [("256", 75), ("-1", 75), ("250 + 6", 75)] {
        let src = format!(
            "main(m: MainArgs) -> int {{\n  m.stdout <- \"x\";\n  0\n}}\n\
             test {{ \"\" -> {{ stdout: \"x\\n\", status: 0 }}, \
             \"\" -> {{ stdout: \"x\\n\", status: {status} }} }}\n"
        );
        // The lines come in source order: both rows, then the error at the status.
        let got = checks(&src);
        assert_eq!(got.len(), 3, "{got:?}");
        assert_eq!(
            got[2].lines().next(),
            Some(
                format!(
                    "5:{col}: A row of `main` expects the exit status `{status}`, and an exit \
                     status is an `int` from 0 to 255."
                )
                .as_str()
            ),
            "{got:?}"
        );
        assert!(
            got[..2]
                .iter()
                .all(|l| l.ends_with("of `main`: not run, since the unit is rejected")),
            "{got:?}"
        );
    }
}

#[test]
fn a_main_value_is_a_record_of_outputs_and_a_tuple_is_refused() {
    // DESIGN.md: a row's value is the standard output or the record `{ stdout:, stderr:,
    // status: }`; a tuple is refused with the record as the repair, as a key's is (plan row
    // MAIN-test-value-record).
    let head = "main(m: MainArgs) -> int {\n  m.stdout <- \"x\";\n  0\n}\n";
    let got = checks(&format!("{head}test {{ \"\" -> (\"x\\n\", \"\", 0) }}\n"));
    // The lines come in source order: the row at 5:8, then the error at the tuple.
    assert_eq!(got.len(), 2, "{got:?}");
    assert!(
        got[1].starts_with(
            "5:14: the expected value of a row of `main` is a String or a record of the run's \
             outputs, not a tuple: repair: write `{ stdout: …, stderr: …, status: … }`"
        ),
        "{got:?}"
    );
    assert!(
        got[0].ends_with("of `main`: not run, since the unit is rejected"),
        "{got:?}"
    );
    let got = checks(&format!(
        "{head}test {{ \"\" -> {{ stdout: \"x\\n\", exit: 0 }} }}\n"
    ));
    assert!(
        got.iter()
            .any(|l| l.contains("`exit` is not an output of a run")),
        "{got:?}"
    );
    let got = checks(&format!(
        "{head}test {{ \"\" -> {{ stdout: \"x\\n\", stdout: \"y\" }} }}\n"
    ));
    // Refused where the record is read, with the note at the first field (QUESTIONS A111).
    assert!(
        got.iter()
            .any(|l| l.contains("the field `stdout` is given twice")
                && l.contains("the first field `stdout`")),
        "{got:?}"
    );
    // The record's fields in any order, any of them left out.
    let got = checks(&format!(
        "{head}test {{ \"\" -> {{ status: 0, stdout: \"x\\n\" }}, \"\" -> {{ stdout: \"x\\n\" }} }}\n"
    ));
    assert_eq!(got, ["5:8: ok", "5:44: ok"]);
}

#[test]
fn a_main_key_that_is_a_tuple_is_rejected() {
    // A tuple of more items than the four inputs is refused as any tuple is, with the note
    // of the four fields (plan row DESIGN-main-key-record-vs-tuple).
    let src = "main(m: MainArgs) {\n  m.stdout <- \"x\";\n}\n\
               test { (\"\", \"\", {}, {}, \"\") -> \"x\\n\" }\n";
    let got = checks(src);
    // The rejection rejects the unit, so the row is also reported as not run.
    assert_eq!(got.len(), 2, "{got:?}");
    assert!(
        got[1].ends_with("of `main`: not run, since the unit is rejected"),
        "{got:?}"
    );
    assert!(
        got[0].contains(
            "a test key of `main` is a String or a record of the run's inputs, not a tuple: \
             repair: write `{ stdin: …, args: …, env: …, files: … }`, the fields in any order \
             and any of them left out; a key has at most the four fields `stdin`, `args`, `env` \
             and `files`"
        ),
        "{got:?}"
    );
}
