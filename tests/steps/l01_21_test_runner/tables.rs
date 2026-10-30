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
    let src = "first(positional s) = s[1] test { \"ab\" -> \"a\" }\n";
    let got = checks(src);
    assert_eq!(got.len(), 1);
    assert!(
        got[0].starts_with("1:35: `\"ab\" -> \"a\"` of `first`: "),
        "{got:?}"
    );
    assert!(!got[0].ends_with(": ok"), "{got:?}");
}

#[test]
fn a_main_row_compares_the_bytes_each_port_writes() {
    let src = "main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- upper(stdin[1]);\n}\n\
               test { \"abc\\n\" -> \"ABC\\n\", \"abc\" -> \"ABC\" }\n";
    assert_eq!(
        checks(src),
        [
            "4:8: ok",
            "4:28: `\"abc\" -> \"ABC\"` of `main`: port `stdout` writes \"ABC\\n\"",
        ]
    );
}

#[test]
fn a_port_not_pushed_writes_nothing() {
    let src = "main(stdin: Lines) -> (stdout: Lines, stderr: Lines) {\n  \
               stdout <- stdin[1];\n}\n\
               test { \"a\" -> (\"a\\n\", \"\"), \"a\" -> (\"a\\n\", \"warning\\n\") }\n";
    assert_eq!(
        checks(src),
        [
            "4:8: ok",
            "4:28: `\"a\" -> (\"a\\n\", \"warning\\n\")` of `main`: port `stderr` writes \"\"",
        ]
    );
}

#[test]
fn a_files_port_is_given_as_a_function_of_the_path() {
    let src = "main(fs: Files) -> (stdout: Lines) {\n  \
               stdout <- fs[\"a.txt\"] ++ fs[\"b.txt\"];\n}\n\
               test { (p -> if p == \"a.txt\" { \"1\" } else { \"2\" }) -> \"12\\n\" }\n";
    assert_eq!(checks(src), ["4:8: ok"]);
}

#[test]
fn a_row_of_the_wrong_shape_says_what_a_port_takes() {
    let src = "main(stdin: Lines) -> (stdout: Lines, stderr: Lines) {\n  \
               stdout <- \"x\";\n  stderr <- \"y\";\n}\n\
               test { 3 -> (\"x\\n\", \"y\\n\"), \"\" -> \"x\\n\", \"\" -> (\"x\\n\", 2) }\n";
    assert_eq!(
        checks(src),
        [
            "5:8: `3 -> (\"x\\n\", \"y\\n\")` of `main`: the `Lines` port `stdin` is given as a \
             String, not 3",
            "5:29: `\"\" -> \"x\\n\"` of `main`: the expected value is a String for each of the \
             2 output ports, not \"x\\n\"",
            "5:42: `\"\" -> (\"x\\n\", 2)` of `main`: the expected value of port `stderr` is a \
             String, not 2",
        ]
    );
}

#[test]
fn a_wave_that_aborts_fails_its_row() {
    let src = "main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- int(stdin[1]);\n}\n\
               test { \"7\" -> \"7\\n\" }\n";
    assert_eq!(
        checks(src),
        ["4:8: `\"7\" -> \"7\\n\"` of `main`: port `stdout` takes strings; 7 was pushed"]
    );
}

#[test]
fn a_main_whose_ports_are_not_l1_reports_once_and_runs_no_row() {
    let src = "main(n: int) -> (stdout: Lines) {\n  stdout <- \"x\";\n}\n\
               test { 1 -> \"x\\n\" }\n";
    assert_eq!(
        checks(src),
        ["1:1: port `n` of `main` is `Lines` or `Files` at layer L1"]
    );
}
