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
        (
            2,
            "",
            "the program reads the environment variable `ZED_B`, and its value is not UTF-8 \
             text, which a Zed string must be. Set `ZED_B` to UTF-8 text before running, or \
             unset it, which the program reads as `#notFound`.\n"
        )
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
fn a_miss_left_undisposed_is_rejected_before_the_run() {
    // `env[name]` is `String | #notFound` (sec:type_language, `->?`), and a `Lines` port takes
    // no `#notFound`, so the program is rejected whether or not the variable is set.
    let src = "main(m: MainArgs) {\n  m.stdout <- m.env[\"ZED_A\"];\n}\n";
    for given in [&[("ZED_A", &b"/h"[..])][..], &[]] {
        let out = run("undisposed", src, given);
        assert_eq!((out.status, out.stdout.as_str()), (1, ""), "{}", out.stderr);
        assert!(
            out.stderr.contains(
                "2:15: a `Lines` port takes a `String` or a family of strings, not \
                 String | #notFound"
            ) && out
                .stderr
                .contains("this expression gives String | #notFound"),
            "{}",
            out.stderr
        );
    }
}

#[test]
fn the_environment_is_a_field_of_main_args() {
    // A parameter of `main` other than `m: MainArgs` is refused, an old environment port among
    // them, whatever its type.
    for ty in [
        "String ->? String",
        "String ->? int",
        "int ->? String",
        "String -> String",
    ] {
        let src = format!("main(env: {ty}) {{\n}}\n");
        let out = run("other_lookup", &src, &[]);
        assert_eq!(out.status, 1, "{ty}");
        assert!(
            out.stderr.contains(&format!(
                "1:6: the parameter `env` of `main` is declared as `env: {ty}`, and `main` takes \
                 one argument, of type `MainArgs`"
            )),
            "{ty}: {}",
            out.stderr
        );
    }
}

#[test]
fn a_main_row_gives_the_environment_as_a_function() {
    let src = format!(
        "{TWO}test {{ (\"\", \"\", (n -> if n == \"ZED_A\" {{ \"1\" }} else {{ #notFound }})) -> \"1|-\\n\", \
         (\"\", \"\", (n -> \"v\")) -> \"v|v\\n\", (\"\", \"\", (n -> #notFound)) -> \"x\" }}\n"
    );
    let got = checks(&src);
    assert_eq!(got.len(), 3, "{got:?}");
    assert!(
        got[0].ends_with(": ok") && got[1].ends_with(": ok"),
        "{got:?}"
    );
    assert!(got[2].ends_with("`m.stdout` writes \"-|-\\n\""), "{got:?}");
}
