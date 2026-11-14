//! What the oracle reports for each kind of source and each way an engine can differ: a
//! unit's table checks, a rejected unit, a program's writes and its refusal, a program with
//! no writes and one that does not load, and the layers of the corpus's programs.

use zed_kernel::{Evaluator, Term, Value};
use zed_tests::oracle::{Engine, labeled, program, unit};
use zedc::run;

/// An engine that gives no value.
fn refuse(_: &Term, _: &mut Evaluator) -> Result<Value, String> {
    Err("refused".into())
}

/// The interpreter and an engine that gives no value.
const ENGINES: &[Engine<'_>] = &[("the interpreter", &run::direct), ("refuse", &refuse)];

#[test]
fn the_table_checks_are_compared_under_each_engine() {
    // `double` is a function, so no binding is compared, only the checks.
    let r = unit("double(positional x) = x * 2\ntest { 1 -> 2 }\n", ENGINES);
    assert_eq!(r.compared, 2);
    assert_eq!(r.not_compared, Vec::<String>::new());
    assert_eq!(r.mismatches.len(), 1, "{:?}", r.mismatches);
    let m = &r.mismatches[0];
    assert!(
        m.starts_with("the table checks: the interpreter gives [")
            && m.contains("failure: None")
            && m.contains(", and refuse gives [")
            && m.contains("failure: Some(\"`1 -> 2` of `double`: refused\")"),
        "{m}"
    );
}

#[test]
fn a_rejected_unit_compares_nothing() {
    for text in ["x = ;\n", "y = undefined_name\n"] {
        let r = unit(text, ENGINES);
        assert_eq!(
            (r.compared, r.mismatches.len(), r.not_compared.len()),
            (0, 0, 0),
            "{text:?}"
        );
    }
    // An empty unit is accepted: its checks, none, are compared once under each engine.
    let r = unit("", ENGINES);
    assert_eq!((r.compared, r.mismatches.len()), (2, 0));
}

#[test]
fn a_programs_writes_are_compared_under_each_engine() {
    let (r, want) = program(
        "main(m: MainArgs) {\n  m.stdout <- \"hi\";\n}\n",
        b"",
        ENGINES,
    );
    assert_eq!(want.as_deref(), Some("port `m.stdout` writes \"hi\\n\""));
    assert_eq!(r.compared, 2);
    assert_eq!(
        r.mismatches,
        [
            "the wave: the interpreter gives port `m.stdout` writes \"hi\\n\", and refuse gives \
          the error `refused`"
        ]
    );
}

#[test]
fn a_program_that_writes_nothing_or_does_not_load() {
    let (r, want) = program("main(m: MainArgs) {\n}\n", b"", ENGINES);
    assert_eq!(want.as_deref(), Some("no writes"));
    // The wave still runs `main` through each engine.
    assert_eq!(
        r.mismatches,
        ["the wave: the interpreter gives no writes, and refuse gives the error `refused`"]
    );
    for text in ["main(m: MainArgs) {\n  m.stdout <- x;\n}\n", "x = 1\n", ""] {
        let (r, want) = program(text, b"", ENGINES);
        assert_eq!((r.compared, want), (0, None), "{text:?}");
    }
}

#[test]
fn the_layer_of_each_program_is_read_from_its_first_line() {
    let d = zed_tests::step_helpers::target_tmpdir()
        .join("l01_37")
        .join("labeled");
    std::fs::create_dir_all(&d).unwrap();
    std::fs::write(d.join("b.zed"), "// layer L3\nx = 1\n").unwrap();
    std::fs::write(d.join("a.zed"), "// layer L12 \nx = 1\n").unwrap();
    std::fs::write(d.join("notes.txt"), "not a program\n").unwrap();
    assert_eq!(labeled(&d), [(d.join("a.zed"), 12), (d.join("b.zed"), 3)]);
}
