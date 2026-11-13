//! `main` in every scope (QUESTIONS A68, Q54, DESIGN.md sec:ports): every function reads the
//! file port as `main::files`, in a unit with no `main` too and with `main` in parentheses; no
//! function calls `main` or uses it as a value; and the old call `files()` is gone.

use zed_tests::scaling::{check, inputs};
use zed_tests::step_helpers::l01_21_test_runner::checks;
use zedc::run::load;

use super::{dir, run};

#[test]
fn a_function_other_than_main_reads_main_files() {
    let d = dir("outside_read");
    let a = d.join("a.txt");
    std::fs::write(&a, "hi").unwrap();
    // One helper before `main` and one after it, the second reading in a string hole.
    let src = format!(
        "size(positional p) = main::files[p] else \"none\";\n\
         main(m: MainArgs) {{\n  m.stdout <- size(\"{a}\");\n  \
         m.stderr <- show(\"{b}\");\n}}\n\
         show(positional p) = \"[${{main::files[p] else \"-\"}}]\";\n",
        a = a.display(),
        b = d.join("absent.txt").display()
    );
    let out = run("outside_read", &src, "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (0, "hi\n", "[-]\n")
    );
    // `main` opens the port once, whether its body reads it, a helper does, or both.
    let both = src.replace(
        "  m.stdout <- size(",
        "  fs = main::files;\n  m.stderr <- fs[\"x\"] else \"\";\n  m.stdout <- size(",
    );
    let program = load(both.as_bytes()).unwrap();
    let files: Vec<_> = (program.inputs().iter())
        .filter(|(p, _)| p == "main::files")
        .collect();
    assert_eq!(files.len(), 1, "{:?}", program.inputs());
    // A program whose functions never read a file has no file port.
    let program =
        load(b"f(positional x) = x ++ \"!\";\nmain(m: MainArgs) {\n  m.stdout <- f(\"a\");\n}\n")
            .unwrap();
    assert!(
        !program.inputs().iter().any(|(p, _)| p == "main::files"),
        "{:?}",
        program.inputs()
    );
}

#[test]
fn a_call_of_main_is_rejected_anywhere() {
    for (name, src, at) in [
        (
            "call_from_helper",
            "f() = main(1);\nmain(m: MainArgs) {\n  m.stdout <- \"x\";\n}\n",
            "1:7",
        ),
        (
            "call_from_main",
            "main(m: MainArgs) {\n  m.stdout <- \"x\";\n  n = main(m);\n}\n",
            "3:7",
        ),
        (
            "call_before_main",
            "g(positional s) = main(s) ++ \"!\";\nmain() {\n}\n",
            "1:19",
        ),
    ] {
        let out = run(name, src, "", &[]);
        assert_eq!((out.status, out.stdout.as_str()), (1, ""), "{name}");
        for part in [
            format!(
                "{at}: Call of `main`: no function calls `main`, which runs once, when the \
                 program starts.\n"
            ),
            format!("{at}: repair: read `main::args` for the argument `main` takes\n"),
            format!(
                "{at}: repair: move the code the call wants into a function that `main` and the \
                 caller both call\n"
            ),
        ] {
            assert!(out.stderr.contains(&part), "{name}: {}", out.stderr);
        }
    }
}

#[test]
fn the_old_call_files_is_rejected_with_main_files() {
    for (name, src, at) in [
        (
            "old_files",
            "main(m: MainArgs) {\n  fs = files();\n  m.stdout <- fs[\"a\"] else \"\";\n}\n",
            "2:8",
        ),
        (
            "old_files_call",
            "f(positional p) = files()(p) else \"\";\nmain(m: MainArgs) {\n  \
             m.stdout <- f(\"a\");\n}\n",
            "1:19",
        ),
    ] {
        let out = run(name, src, "", &[]);
        assert_eq!((out.status, out.stdout.as_str()), (1, ""), "{name}");
        for part in [
            format!("{at}: `files` is not defined: the file port is `main::files`.\n"),
            format!("{at}: repair: `main::files` for `files()`, as in `fs = main::files;`\n"),
            format!("{at}: repair: `main::files[path]` for `files()(path)`\n"),
        ] {
            assert!(out.stderr.contains(&part), "{name}: {}", out.stderr);
        }
    }
    // A program's own `files` is an ordinary name.
    let out = run(
        "own_files",
        "files(positional s) = s ++ \"!\";\nmain(m: MainArgs) {\n  m.stdout <- files(\"a\");\n}\n",
        "",
        &[],
    );
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (0, "a!\n", "")
    );
}

#[test]
fn main_files_in_a_unit_without_main_names_the_programs_port() {
    // A library reads the program's file port as every function does (QUESTIONS Q54); its
    // test table's clause gives the port to its rows, and a row of a table without the clause
    // fails at the read, naming the repair.
    let src = "size(positional p) = main::files[p] else \"none\"\n  \
               test with main::files = q -> if q == \"a\" { \"x\" } else { #notFound } \
               { \"a\" -> \"x\", \"b\" -> \"none\", \"a\" -> \"y\" }\n  \
               test { \"a\" -> \"x\" }\n\
               show(positional p) = \"[${(main)::files[p] else \"-\"}]\"\n  \
               test with main::files = (q -> \"1\") { \"a\" -> \"[1]\" }\n";
    assert_eq!(
        checks(src),
        [
            "2:73: ok",
            "2:85: ok",
            "2:100: `\"a\" -> \"y\"` of `size`: the result is \"x\"",
            "3:10: `\"a\" -> \"x\"` of `size`: the port `main::files` could not answer a read: \
             the table gives the row no files; repair: `test with main::files = p -> …` on the \
             table, a function from a path to its text",
            "5:40: ok",
        ]
    );
}

#[test]
fn main_files_in_parentheses_is_main_files() {
    // Parentheses around `main` change nothing, in `main`'s body, before it and after it, and
    // `main` opens the port once.
    let d = dir("outside_parens");
    let a = d.join("a.txt");
    std::fs::write(&a, "hi").unwrap();
    let src = format!(
        "size(positional p) = (main)::files[p] else \"none\";\n\
         main(m: MainArgs) {{\n  fs = ((main))::files;\n  \
         m.stdout <- size(\"{a}\") ++ (fs[\"{a}\"] else \"-\") ++ show(\"{a}\");\n}}\n\
         show(positional p) = \"[${{(main)::files[p] else \"-\"}}]\";\n",
        a = a.display(),
    );
    let out = run("outside_parens", &src, "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (0, "hihi[hi]\n", "")
    );
    let program = load(src.as_bytes()).unwrap();
    let files: Vec<_> = (program.inputs().iter())
        .filter(|(p, _)| p == "main::files")
        .collect();
    assert_eq!(files.len(), 1, "{:?}", program.inputs());
}

#[test]
fn main_used_as_a_value_is_rejected_anywhere() {
    // A value of `main` could be called later, so every use of `main` but a call and a read
    // `main::…` is rejected, whether a call through it follows or not.
    for (name, src, at) in [
        (
            "value_bound",
            "f = main;\ng() = f(1);\nmain(m: MainArgs) {\n  m.stdout <- \"x\";\n}\n",
            "1:5",
        ),
        (
            "value_passed",
            "h(positional k) = k(1);\ng() = h(main);\nmain() {\n}\n",
            "2:9",
        ),
        (
            "value_passed_in_main",
            "h(positional k) = k(1);\nmain(m: MainArgs) {\n  m.stdout <- \"x\";\n  \
             n = h(main);\n}\n",
            "4:9",
        ),
        ("value_returned", "g() = main;\nmain() {\n}\n", "1:7"),
        (
            "value_in_parentheses_in_a_tuple",
            "g() = (1, (main));\nmain() {\n}\n",
            "1:11",
        ),
    ] {
        let out = run(name, src, "", &[]);
        assert_eq!((out.status, out.stdout.as_str()), (1, ""), "{name}");
        for part in [
            format!(
                "{at}: `main` used as a value: no function calls `main`, which runs once, when \
                 the program starts.\n"
            ),
            format!("{at}: repair: read `main::args` or `main::files` for what `main` reads\n"),
            format!(
                "{at}: repair: in place of `main`, use a function that `main` and this code \
                 both call\n"
            ),
        ] {
            assert!(out.stderr.contains(&part), "{name}: {}", out.stderr);
        }
        assert!(
            !out.stderr.contains("Call of `main`"),
            "{name}: {}",
            out.stderr
        );
    }
    // A call of `main`, in parentheses or not, is rejected once, as a call.
    let out = run(
        "call_in_parentheses",
        "g() = (main)(1);\nmain() {\n}\n",
        "",
        &[],
    );
    assert_eq!(out.status, 1);
    assert!(
        out.stderr.contains("1:7: Call of `main`") && !out.stderr.contains("used as a value"),
        "{}",
        out.stderr
    );
}

#[test]
fn a_keyed_write_to_main_files_is_a_later_step_in_main_and_outside_it() {
    // A write `fs[path] <- v` to the file port is step L7.2's keyed push, the same in `main`
    // and in another function.
    for (name, src, at) in [
        (
            "keyed_write_outside",
            "w() {\n  main::files[\"x\"] <- \"v\";\n}\nmain(m: MainArgs) {\n  \
             m.stdout <- \"x\";\n}\n",
            "2:3",
        ),
        (
            "keyed_write_in_main",
            "main(m: MainArgs) {\n  main::files[\"x\"] <- \"v\";\n  m.stdout <- \"x\";\n}\n",
            "2:3",
        ),
    ] {
        let out = run(name, src, "", &[]);
        assert_eq!((out.status, out.stdout.as_str()), (1, ""), "{name}");
        assert!(
            out.stderr.contains(&format!(
                "{at}: the push at a key `main::files[\"x\"] <- \"v\";` is part of the Zed \
                 language, and this version of zedc does not compile it yet."
            )),
            "{name}: {}",
            out.stderr
        );
    }
}

#[test]
fn a_record_of_a_helper_read_replays_and_names_main_files() {
    let d = dir("outside_record");
    let a = d.join("a.txt");
    std::fs::write(&a, "hi").unwrap();
    let rec = d.join("run.record");
    let src = format!(
        "size(positional p) = main::files[p] else \"none\";\n\
         main(m: MainArgs) {{\n  m.stdout <- size(\"{}\");\n}}\n",
        a.display()
    );
    let out = run(
        "outside_record",
        &src,
        "",
        &["--record", rec.to_str().unwrap()],
    );
    assert_eq!((out.status, out.stdout.as_str()), (0, "hi\n"));
    let program = load(src.as_bytes()).unwrap();
    let record = zedc::run::Record::from_bytes(&std::fs::read(&rec).unwrap()).unwrap();
    assert_eq!(record.files["main::files"].len(), 1);
    let wave = program.replay(&record).unwrap();
    assert_eq!(wave.writes[0].1, b"hi\n");
}

/// `n` helpers before `main` and `n` after it, each reading `main::files` once, and `main`
/// calling each.
fn helpers(n: usize) -> String {
    let mut src = String::new();
    for i in 0..n {
        src.push_str(&format!("b{i}(positional p) = main::files[p] else \"\";\n"));
    }
    src.push_str("main(m: MainArgs) {\n  m.stdout <- \"\"");
    for i in 0..n {
        src.push_str(&format!(" ++ b{i}(\"x\") ++ a{i}(\"y\")"));
    }
    src.push_str(";\n}\n");
    for i in 0..n {
        src.push_str(&format!("a{i}(positional p) = main::files[p] else \"\";\n"));
    }
    src
}

#[test]
fn reads_of_main_files_outside_main_load_in_linear_time() {
    // The builder finds the reads outside `main` in one walk of the tree before it builds
    // `main`'s header, and the resolver gives each its port in constant time.
    let srcs = inputs(100, helpers);
    check("loading n helpers that read main::files", 100, |n| {
        let program = load(srcs[&n].as_bytes()).unwrap();
        assert!(program.inputs().iter().any(|(p, _)| p == "main::files"));
    });
}
