//! Completeness of step L1.19c (plan row TEST-complete-ports, COMPLETENESS.md beside this
//! file): names and values of each kind, and a read in each position an expression takes. A
//! failing case names itself; all cases of a table run before the test reports.

use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt;

use super::{TWO, dir_program, run_words, zedc};

/// One variable as the process holds it, from bytes.
fn var(name: &[u8], value: &[u8]) -> (OsString, OsString) {
    (
        OsString::from_vec(name.to_vec()),
        OsString::from_vec(value.to_vec()),
    )
}

/// Runs each case `(name, program, words after the file, variables, status, standard
/// output)` and asserts the status and output of every one, naming each case that differs.
#[allow(clippy::type_complexity)]
fn expect(table: &str, cases: Vec<(&str, &str, &[&str], Vec<(OsString, OsString)>, u8, &str)>) {
    let mut wrong = Vec::new();
    for (name, src, more, env, status, stdout) in cases {
        let prog = dir_program(&format!("{table}_{name}"), src);
        let out = zedc(&run_words(&prog, more), env);
        if (out.status, out.stdout.as_str()) != (status, stdout) {
            wrong.push(format!(
                "{name}: gave status {} and {:?}, expected {status} and {stdout:?}\n{}",
                out.status, out.stdout, out.stderr
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// `main` writing `expr` to standard output.
fn writes(expr: &str) -> String {
    format!("main(m: MainArgs) {{\n  m.stdout <- {expr};\n}}\n")
}

#[test]
fn names_and_values_of_each_kind() {
    let read = |name: &str| writes(&format!("m.env[\"{name}\"] else \"-\""));
    let (a, empty_name, with_equals, lower, unicode_name) = (
        read("ZED_A"),
        read(""),
        read("ZED_A=x"),
        read("zed_a"),
        read("ZED_\u{e9}"),
    );
    expect(
        "kinds",
        vec![
            (
                "non_ascii_value",
                &a,
                &[],
                vec![var(b"ZED_A", "h\u{e9}\u{1d11e}".as_bytes())],
                0,
                "h\u{e9}\u{1d11e}\n",
            ),
            (
                "value_with_equals",
                &a,
                &[],
                vec![var(b"ZED_A", b"k=v=w")],
                0,
                "k=v=w\n",
            ),
            (
                "value_with_spaces",
                &a,
                &[],
                vec![var(b"ZED_A", b" a b ")],
                0,
                " a b \n",
            ),
            (
                "value_with_a_line_end",
                &a,
                &[],
                vec![var(b"ZED_A", b"a\nb")],
                0,
                "a\nb\n",
            ),
            (
                "empty_name_is_never_set",
                &empty_name,
                &[],
                vec![var(b"ZED_A", b"x")],
                0,
                "-\n",
            ),
            (
                "name_holding_equals",
                &with_equals,
                &[],
                vec![var(b"ZED_A", b"x=y")],
                0,
                "-\n",
            ),
            (
                "names_are_case_sensitive",
                &lower,
                &[],
                vec![var(b"ZED_A", b"x")],
                0,
                "-\n",
            ),
            (
                "non_ascii_name",
                &unicode_name,
                &[],
                vec![var("ZED_\u{e9}".as_bytes(), b"v")],
                0,
                "v\n",
            ),
            (
                "unread_name_not_utf8",
                &a,
                &[],
                vec![var(b"ZED_A", b"ok"), var(b"ZED_\xff", b"x")],
                0,
                "ok\n",
            ),
            ("no_variables_at_all", &a, &[], vec![], 0, "-\n"),
        ],
    );
}

#[test]
fn a_variable_is_read_in_each_position() {
    let twice = writes("\"${m.env[\"ZED_A\"] else \"-\"}${m.env[\"ZED_A\"] else \"-\"}\"");
    let condition = writes("if (m.env[\"ZED_A\"] else \"\") == \"1\" { \"on\" } else { \"off\" }");
    let by_argument = writes("m.env[m.args[0] else \"\"] else \"-\"");
    let helper = "get(e: String ->? String, n: String) = e[n] else \"-\";\n\
                  main(m: MainArgs) {\n  m.stdout <- get(e: m.env, n: \"ZED_A\");\n}\n";
    let as_int = writes("\"${(int(m.env[\"ZED_A\"] else \"\") else 0) * 2}\"");
    let atom_else = writes("m.env[\"ZED_A\"] else #notFound -> \"unset\"");
    expect(
        "position",
        vec![
            (
                "read_twice",
                &twice,
                &[],
                vec![var(b"ZED_A", b"a")],
                0,
                "aa\n",
            ),
            (
                "condition_true",
                &condition,
                &[],
                vec![var(b"ZED_A", b"1")],
                0,
                "on\n",
            ),
            ("condition_unset", &condition, &[], vec![], 0, "off\n"),
            (
                "name_from_an_argument",
                &by_argument,
                &["--", "ZED_B"],
                vec![var(b"ZED_B", b"b")],
                0,
                "b\n",
            ),
            (
                "name_from_no_argument",
                &by_argument,
                &[],
                vec![var(b"ZED_B", b"b")],
                0,
                "-\n",
            ),
            (
                "helper_parameter",
                helper,
                &[],
                vec![var(b"ZED_A", b"h")],
                0,
                "h\n",
            ),
            (
                "cast_to_int",
                &as_int,
                &[],
                vec![var(b"ZED_A", b"21")],
                0,
                "42\n",
            ),
            (
                "cast_that_fails",
                &as_int,
                &[],
                vec![var(b"ZED_A", b"x")],
                0,
                "0\n",
            ),
            (
                "atom_else_set",
                &atom_else,
                &[],
                vec![var(b"ZED_A", b"s")],
                0,
                "s\n",
            ),
            ("atom_else_unset", &atom_else, &[], vec![], 0, "unset\n"),
            (
                "two_names_one_bad_and_read",
                TWO,
                &[],
                vec![var(b"ZED_A", b"\xff"), var(b"ZED_B", b"b")],
                2,
                "",
            ),
        ],
    );
}

#[test]
fn a_record_keeps_each_kind_of_value() {
    let src = writes("\"${m.env[\"ZED_A\"] else \"-\"}|${m.env[\"\"] else \"-\"}\"");
    let prog = dir_program("record_kinds", &src);
    let rec = zed_tests::step_helpers::l01_19a_command_line::dir("l01_19c_record_kinds")
        .join("wave.rec")
        .into_os_string()
        .into_string()
        .unwrap();
    let value = "h\u{e9} =\nx";
    let out = zedc(
        &run_words(&prog, &["--record", &rec]),
        vec![var(b"ZED_A", value.as_bytes())],
    );
    let expected = format!("{value}|-\n");
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, expected.as_str()),
        "{}",
        out.stderr
    );
    let words = [OsString::from("replay"), prog, OsString::from(&rec)];
    let out = zedc(&words, vec![]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, expected.as_str()),
        "{}",
        out.stderr
    );
}
