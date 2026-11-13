//! A table's clause `test with p = e, … { rows }`, which gives a port its value while each row
//! runs (QUESTIONS A66). This zedc has no store, no `now` and no top-level port, so the ports a
//! clause gives here are `main`'s inputs, and on another function's table the file port
//! `main::files`, which every function reads (QUESTIONS A68); the other names are refused or
//! rejected.

use super::checks;

#[test]
fn a_clause_gives_main_its_files() {
    // The total of an order, read from the file the clause gives; a row the clause's files
    // leave out reads `#notFound`, and a wrong expected value fails its row.
    let src = "main(m: MainArgs) {\n  \
               m.stdout <- main::files[m.stdin[0] else \"\"] else \"0\";\n}\n\
               test with main::files = p -> if p == \"7\" { \"12\" } else { #notFound } \
               { \"7\" -> \"12\\n\", \"8\" -> \"0\\n\", \"7\" -> \"13\\n\" }\n";
    assert_eq!(
        checks(src),
        [
            "4:72: ok",
            "4:87: ok",
            "4:101: `\"7\" -> \"13\\n\"` of `main`: `m.stdout` writes \"12\\n\"",
        ]
    );
}

#[test]
fn each_clause_holds_for_its_own_rows() {
    // The rows of a table without a clause, and of one before or after it, read no file.
    let src = "main(m: MainArgs) {\n  m.stdout <- main::files[\"a\"] else \"none\";\n}\n\
               test { \"\" -> \"none\\n\" }\n\
               test with main::files = (p -> \"1\") { \"\" -> \"1\\n\", \"x\" -> \"1\\n\" }\n\
               test with main::files = (p -> \"2\") { \"\" -> \"2\\n\" }\n\
               test { \"\" -> \"none\\n\" }\n";
    assert_eq!(
        checks(src),
        ["4:8: ok", "5:38: ok", "5:51: ok", "6:38: ok", "7:8: ok"]
    );
}

#[test]
fn a_clause_gives_the_arguments_and_the_environment() {
    // The key gives standard input, and the clause the rest.
    let src = "main(m: MainArgs) {\n  \
               m.stdout <- (m.stdin[0] else \"\") ++ (m.args[0] else \"\");\n  \
               m.stderr <- m.env(\"HOME\") else \"none\";\n}\n\
               test with main::args = \"q\\n\", \
               main::env = n -> if n == \"HOME\" { \"/h\" } else { #notFound } \
               { \"a\" -> (\"aq\\n\", \"/h\\n\"), \"b\" -> (\"bq\\n\", \"none\\n\") }\n";
    assert_eq!(
        checks(src),
        [
            "5:93: ok",
            "5:118: `\"b\" -> (\"bq\\n\", \"none\\n\")` of `main`: `m.stderr` writes \"/h\\n\"",
        ]
    );
}

#[test]
fn a_row_that_writes_a_port_compares_its_writes_and_status() {
    // `main`'s value is the record of its writes: what each output port is written, and the
    // status.
    let src = "main(m: MainArgs) -> int {\n  \
               fs = main::files;\n  \
               m.stdout <- fs[\"a\"] else \"\";\n  \
               m.stderr <- fs[\"b\"] else \"no b\";\n  \
               if (fs[\"b\"] else \"\") == \"\" { 1 } else { 0 }\n}\n\
               test with main::files = (p -> if p == \"a\" { \"x\" } else { #notFound }) \
               { \"\" -> (\"x\\n\", \"no b\\n\", 1), \"\" -> (\"x\\n\", \"no b\\n\") }\n";
    assert_eq!(
        checks(src),
        [
            "7:73: ok",
            "7:101: `\"\" -> (\"x\\n\", \"no b\\n\")` of `main`: the run exits with status 1",
        ]
    );
}

#[test]
fn an_input_given_by_the_key_and_the_clause_is_rejected() {
    let src = "main(m: MainArgs) {\n  m.stdout <- main::files[\"a\"] else \"\";\n}\n\
               test with main::files = (p -> \"1\") \
               { (\"\", \"\", (n -> #notFound), (p -> \"2\")) -> \"2\\n\" }\n";
    let got = checks(src);
    assert_eq!(
        got[0],
        "4:38: this row's key gives `main::files`, and so does its table's `test with`; give it \
         once, in the key or in the clause."
    );
    assert_eq!(got.len(), 2, "{got:?}");
}

/// The headline and notes of the one rejection `src` gets, with the rows it leaves unrun.
fn rejected(src: &str) -> String {
    let got = checks(src);
    assert!(
        (got.iter().skip(1)).all(|g| g.ends_with("not run, since the unit is rejected")),
        "{got:?}"
    );
    got[0].clone()
}

#[test]
fn a_name_that_is_no_port_is_rejected_with_the_ports_of_main() {
    let got = rejected(
        "main(m: MainArgs) {\n  m.stdout <- \"a\";\n}\n\
         test with stdin = \"x\" { \"\" -> \"a\\n\" }\n",
    );
    assert!(
        got.starts_with("4:11: `stdin` in `test with` is not a port."),
        "{got}"
    );
    for f in ["stdin", "args", "env", "files"] {
        assert!(got.contains(&format!("repair: `main::{f} = …`")), "{got}");
    }
}

#[test]
fn a_function_of_the_program_is_no_port() {
    // A test gives a port its value, and never replaces the program's own code.
    let got = rejected(
        "f(positional x) = x + 1;\ng(positional x) = f(x) test with f = (y -> y) { 1 -> 2 }\n",
    );
    assert!(
        got.starts_with("2:34: `f` in `test with` is not a port."),
        "{got}"
    );
    assert!(got.contains("`f` is a value the program computes"), "{got}");
    assert!(
        got.contains("repair: `main::files = …`, the file port, which every function reads"),
        "{got}"
    );
    assert!(
        got.contains("repair: `test { … }`, the table without `f = …`"),
        "{got}"
    );
}

#[test]
fn a_name_that_names_nothing_is_no_port() {
    let got = rejected("h(positional x) = x + 1 test with zork = 1 { 1 -> 2 }\n");
    assert!(
        got.starts_with("1:35: `zork` in `test with` is not a port."),
        "{got}"
    );
    assert!(!got.contains("computes"), "{got}");
}

#[test]
fn a_field_of_main_that_is_no_input_is_rejected() {
    let got = rejected(
        "main(m: MainArgs) {\n  m.stdout <- \"a\";\n}\n\
         test with main::foo = \"x\" { \"\" -> \"a\\n\" }\n",
    );
    assert!(
        got.starts_with("4:11: `main::foo` in `test with` is not a port of `main`."),
        "{got}"
    );
    assert!(got.contains("repair: `main::files = …`"), "{got}");
}

#[test]
fn a_port_given_twice_is_rejected() {
    let got = rejected(
        "main(m: MainArgs) {\n  m.stdout <- m.args[0] else \"\";\n}\n\
         test with main::args = \"a\", main::args = \"b\" { \"\" -> \"a\\n\" }\n",
    );
    assert!(
        got.starts_with("4:29: `main::args` is given twice in this `test with`."),
        "{got}"
    );
    assert!(got.contains("repair: remove one of the two"), "{got}");
}

#[test]
fn the_ports_this_zedc_has_not_are_refused() {
    // The clock (DESIGN's `late`), an output of `main`, and an input of `main` other than
    // `main::files` on another function's table.
    for (src, what) in [
        (
            "late(positional t) = t test with now = () -> 3 { 1 -> 1 }\n",
            "1:34: a test clause giving the prelude port `now`",
        ),
        (
            "main(m: MainArgs) {\n  m.stdout <- \"a\";\n}\n\
             test with main::stdout = \"a\\n\" { \"\" -> \"a\\n\" }\n",
            "4:11: a test clause giving `main::stdout`",
        ),
        (
            "f(positional x) = x test with main::args = \"a\" { 1 -> 1 }\n",
            "1:31: in the table of a function other than `main`, a test clause giving \
             `main::args`",
        ),
    ] {
        let got = rejected(src);
        assert!(
            got.starts_with(&format!("{what} is part of the Zed language")),
            "{got}"
        );
    }
}

#[test]
fn a_clause_gives_another_function_its_files() {
    // A function other than `main` reads the file port as `main::files` (QUESTIONS A68), and
    // its table's clause gives it; a wrong expected value fails its row, and a row of a table
    // without the clause fails at the read, naming the repair.
    let src = "size(positional p) = main::files[p] else \"none\"\n  \
               test with main::files = q -> if q == \"a\" { \"x\" } else { #notFound } \
               { \"a\" -> \"x\", \"b\" -> \"none\", \"a\" -> \"y\" }\n  \
               test { \"a\" -> \"x\" }\n\
               main(m: MainArgs) {\n  m.stdout <- size(\"a\");\n}\n";
    assert_eq!(
        checks(src),
        [
            "2:73: ok",
            "2:85: ok",
            "2:100: `\"a\" -> \"y\"` of `size`: the result is \"x\"",
            "3:10: `\"a\" -> \"x\"` of `size`: the port `main::files` could not answer a read: \
             the table gives the row no files; repair: `test with main::files = p -> …` on the \
             table, a function from a path to its text",
        ]
    );
}

#[test]
fn a_clause_on_a_function_that_reads_no_file_changes_nothing() {
    let src = "inc(positional x) = x + 1 test with main::files = (p -> \"1\") { 1 -> 2, 2 -> 4 }\n";
    assert_eq!(
        checks(src),
        ["1:64: ok", "1:72: `2 -> 4` of `inc`: the result is 3"]
    );
}
