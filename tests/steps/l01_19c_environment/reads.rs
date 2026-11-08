//! What a read of the environment gives: a variable's value, the empty value as itself,
//! `#notFound` for a name that is not set, and a usage error for a value that is not UTF-8.

use zed_tests::step_helpers::l01_21_test_runner::checks;

use super::{TWO, run};

#[test]
fn a_program_reads_a_variable() {
    let out = run("value", TWO, &[("ZED_A", b"hello world"), ("ZED_B", b"2")]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "hello world|2\n"),
        "{}",
        out.stderr
    );
}

#[test]
fn an_empty_value_is_the_empty_string() {
    let out = run("empty", TWO, &[("ZED_A", b""), ("ZED_B", b"x")]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "|x\n"),
        "{}",
        out.stderr
    );
}

#[test]
fn a_name_that_is_not_set_misses() {
    let out = run("absent", TWO, &[("ZED_B", b"x"), ("ZED_AA", b"near")]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "-|x\n"),
        "{}",
        out.stderr
    );
}

#[test]
fn a_value_that_is_not_utf8_is_a_usage_error_naming_it() {
    let out = run(
        "not_utf8",
        TWO,
        &[("ZED_A", b"ok"), ("ZED_B", &[b'a', 255])],
    );
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (2, "", "environment variable `ZED_B` is not UTF-8\n")
    );
}

#[test]
fn a_variable_the_program_does_not_read_may_hold_anything() {
    let out = run("unread", TWO, &[("ZED_A", b"a"), ("ZED_C", &[255])]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "a|-\n"),
        "{}",
        out.stderr
    );
}

#[test]
fn a_miss_left_undisposed_stops_the_run() {
    // The checker types a `->?` lookup as its value type alone, not `V | #notFound` as
    // sec:type_language says (follow-up ARROW-partial-notFound), so the miss is found at the
    // push.
    let src = "main(env: String ->? String) -> (stdout: Lines) {\n  stdout <- env[\"ZED_A\"];\n}\n";
    let set = run("undisposed", src, &[("ZED_A", b"/h")]);
    assert_eq!(
        (set.status, set.stdout.as_str()),
        (0, "/h\n"),
        "{}",
        set.stderr
    );
    let unset = run("undisposed", src, &[]);
    assert_eq!(
        (unset.status, unset.stdout.as_str(), unset.stderr.as_str()),
        (1, "", "port `stdout` takes strings; #notFound was pushed\n")
    );
}

#[test]
fn only_a_string_lookup_of_strings_is_the_environment() {
    for ty in ["String ->? int", "int ->? String", "String -> String"] {
        let src = format!("main(env: {ty}) -> (stdout: Lines) {{\n  stdout <- \"\";\n}}\n");
        let out = run("other_lookup", &src, &[]);
        assert_eq!(out.status, 1, "{ty}");
        assert!(
            out.stderr.contains(
                "1:6: port `env` of `main` is `Lines`, `Files`, `CommandLine` or \
                 `String ->? String` at layer L1"
            ),
            "{ty}: {}",
            out.stderr
        );
    }
}

#[test]
fn a_main_row_gives_the_environment_as_a_function() {
    let src = format!(
        "{TWO}test {{ (n -> if n == \"ZED_A\" {{ \"1\" }} else {{ #notFound }}) -> \"1|-\\n\", \
         (n -> \"v\") -> \"v|v\\n\", (n -> #notFound) -> \"x\" }}\n"
    );
    let got = checks(&src);
    assert_eq!(got.len(), 3, "{got:?}");
    assert!(
        got[0].ends_with(": ok") && got[1].ends_with(": ok"),
        "{got:?}"
    );
    assert!(
        got[2].ends_with("port `stdout` writes \"-|-\\n\""),
        "{got:?}"
    );
}
