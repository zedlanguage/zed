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
    let src = "main(m: MainArgs) {\n  m.stdout <- upper(m.stdin[0] else \"\");\n}\n\
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
               m.stdout <- m.stdin[0] else \"\";\n}\n\
               test { \"a\" -> (\"a\\n\", \"\"), \"a\" -> (\"a\\n\", \"warning\\n\") }\n";
    assert_eq!(
        checks(src),
        [
            "4:8: ok",
            "4:28: `\"a\" -> (\"a\\n\", \"warning\\n\")` of `main`: `m.stderr` writes \"\"",
        ]
    );
}

#[test]
fn a_files_port_is_given_as_a_function_of_the_path() {
    let src = "main(m: MainArgs) {\n  fs = files();\n  \
               m.stdout <- (fs[\"a.txt\"] else \"\") ++ (fs[\"b.txt\"] else \"\");\n}\n\
               test { (\"\", \"\", (n -> #notFound), (p -> if p == \"a.txt\" { \"1\" } else { \"2\" })) -> \"12\\n\" }\n";
    assert_eq!(checks(src), ["5:8: ok"]);
}

#[test]
fn a_row_of_the_wrong_shape_says_what_a_port_takes() {
    let src = "main(m: MainArgs) {\n  \
               m.stdout <- \"x\";\n  m.stderr <- \"y\";\n}\n\
               test { 3 -> (\"x\\n\", \"y\\n\"), \"\" -> \"x\\n\", \"\" -> (\"x\\n\", 2) }\n";
    assert_eq!(
        checks(src),
        [
            "5:8: `3 -> (\"x\\n\", \"y\\n\")` of `main`: the `Lines` port `m.stdin` is given as a \
             String, not 3",
            "5:29: ok",
            "5:42: `\"\" -> (\"x\\n\", 2)` of `main`: the expected value of `m.stderr` is a String, \
             not 2",
        ]
    );
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
    assert!(got[0].contains("cannot join"), "{got:?}");
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
    // The third item of the value is the status the run exits with, from 0 to 255.
    let src = "main(m: MainArgs) -> int {\n  m.stdout <- \"x\";\n  \
               if (m.stdin[0] else \"\") == \"no\" { 3 } else { 0 }\n}\n\
               test { \"no\" -> (\"x\\n\", \"\", 3), \"yes\" -> (\"x\\n\", \"\", 3), \
               \"no\" -> (\"x\\n\", \"\", 256) }\n";
    assert_eq!(
        checks(src),
        [
            "5:8: ok",
            "5:32: `\"yes\" -> (\"x\\n\", \"\", 3)` of `main`: the run exits with status 0",
            "5:57: `\"no\" -> (\"x\\n\", \"\", 256)` of `main`: the expected status of a row of \
             `main` is an int from 0 to 255, not 256",
        ]
    );
}

#[test]
fn a_main_key_of_more_than_four_items_is_rejected() {
    let src = "main(m: MainArgs) {\n  m.stdout <- \"x\";\n}\n\
               test { (\"\", \"\", (n -> #notFound), (p -> #notFound), \"\") -> \"x\\n\" }\n";
    let got = checks(src);
    // The rejection rejects the unit, so the row is also reported as not run.
    assert_eq!(got.len(), 2, "{got:?}");
    assert!(
        got[1].ends_with("of `main`: not run, since the unit is rejected"),
        "{got:?}"
    );
    assert!(
        got[0].contains(
            "a test key of `main` is the standard input of the run, as a String, or the tuple \
             `(stdin, args, env, files)` of its inputs, with the items left off its end empty, \
             and this key has 5 items"
        ),
        "{got:?}"
    );
}
