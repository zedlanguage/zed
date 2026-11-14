//! Completeness of step L1.19b (plan row TEST-complete-ports, COMPLETENESS.md beside this
//! file): what the content address covers. DESIGN.md step L1.19: it covers the term `main`
//! runs, closed over the definitions it reaches, and the port declarations, and nothing
//! else, since a definition `main` does not reach cannot change a run.

use zedc::run::load;

/// `main` writing `expr`, after the definitions `defs`.
fn prog(defs: &str, expr: &str) -> String {
    format!("{defs}main(m: MainArgs) {{\n  m.stdout <- {expr};\n}}\n")
}

#[test]
fn what_keeps_the_address_and_what_changes_it() {
    let base = prog("twice(x: int) = x * 2;\n", "\"${twice(x: 3)}\"");
    let cases: Vec<(&str, String, bool)> = vec![
        // Kept: nothing `main` reaches changes.
        ("comment_added", format!("// a note\n{base}"), true),
        (
            "unreached_definition_added",
            prog(
                "twice(x: int) = x * 2;\nunused(x: int) = x + 1;\n",
                "\"${twice(x: 3)}\"",
            ),
            true,
        ),
        (
            "definitions_in_another_order",
            prog(
                "unused(x: int) = x;\ntwice(x: int) = x * 2;\n",
                "\"${twice(x: 3)}\"",
            ),
            true,
        ),
        (
            "parameter_type_left_out",
            "twice(x: int) = x * 2;\nmain(m) {\n  m.stdout <- \"${twice(x: 3)}\";\n}\n".to_string(),
            true,
        ),
        (
            "test_table_added",
            prog(
                "twice(x: int) = x * 2 test { 1 -> 2 }\n",
                "\"${twice(x: 3)}\"",
            ),
            true,
        ),
        // Names are not part of a closed term: a reached helper or its parameter renamed,
        // with every call, runs the same term.
        (
            "reached_helper_renamed",
            prog("double(x: int) = x * 2;\n", "\"${double(x: 3)}\""),
            true,
        ),
        (
            "parameter_of_a_reached_helper_renamed",
            prog("twice(y: int) = y * 2;\n", "\"${twice(y: 3)}\""),
            true,
        ),
        // Changed: the meaning of the term or the ports it reads.
        (
            "reached_helper_body_changed",
            prog("twice(x: int) = x * 3;\n", "\"${twice(x: 3)}\""),
            false,
        ),
        (
            "literal_in_main_changed",
            prog("twice(x: int) = x * 2;\n", "\"${twice(x: 4)}\""),
            false,
        ),
        (
            "written_to_another_port",
            format!(
                "twice(x: int) = x * 2;\nmain(m: MainArgs) {{\n  m.stderr <- \"${{twice(x: 3)}}\";\n}}\n"
            ),
            false,
        ),
        (
            "reads_standard_input",
            prog(
                "twice(x: int) = x * 2;\n",
                "\"${twice(x: 3)}${m.stdin[0] else \"\"}\"",
            ),
            false,
        ),
        (
            "reads_an_argument",
            prog(
                "twice(x: int) = x * 2;\n",
                "\"${twice(x: 3)}${m.args[0] else \"\"}\"",
            ),
            false,
        ),
        (
            "reads_a_variable",
            prog(
                "twice(x: int) = x * 2;\n",
                "\"${twice(x: 3)}${m.env[\"A\"] else \"\"}\"",
            ),
            false,
        ),
    ];
    let address = |src: &str| load(src.as_bytes()).unwrap().address().unwrap();
    let ours = address(&base);
    let mut wrong = Vec::new();
    for (name, src, same) in &cases {
        let theirs = address(src);
        if (theirs == ours) != *same {
            wrong.push(format!(
                "{name}: the address {} kept\n{src}",
                if *same { "was not" } else { "was" }
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn reads_at_other_keys_or_names_have_other_addresses() {
    let address = |expr: &str| load(prog("", expr).as_bytes()).unwrap().address().unwrap();
    let distinct = [
        address("m.stdin[0] else \"\""),
        address("m.stdin[1] else \"\""),
        address("m.args[0] else \"\""),
        address("m.env[\"A\"] else \"\""),
        address("m.env[\"B\"] else \"\""),
        address("main::files[\"A\"] else \"\""),
    ];
    for (i, a) in distinct.iter().enumerate() {
        for (j, b) in distinct.iter().enumerate().skip(i + 1) {
            assert_ne!(a, b, "reads {i} and {j}");
        }
    }
}
