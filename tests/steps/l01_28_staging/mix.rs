//! `mix`: the build evaluates the demanded build-stage definitions and subterms, leaves the
//! port-dependent ones to run, and the staged program writes what the program writes.

use zedc::stage::{BUILD_FUEL, Stage, color};

use super::{out, staged, term};

/// A log filter: the day length and the cutoff are computed at build, the rest per line.
const UPTIME: &str = "day = 60 * 60 * 24;\nweek = 7 * day;\n\
    main(stdin: Lines) -> (stdout: Lines) {\n  \
    secs = int(stdin[1]) else 0;\n  \
    stdout <- String(week - secs) ++ \" left of \" ++ String(week);\n}\n";

#[test]
fn constants_are_computed_at_build() {
    let (p, s, report) = staged(UPTIME, BUILD_FUEL);
    assert_eq!(report.built, ["day", "week"]);
    assert_eq!(term(&s, "week"), "604800");
    assert_eq!(report.unread, Vec::<String>::new());
    assert_eq!(report.left, []);
    for input in ["700000\n", "12\n", "noise\n"] {
        assert_eq!(out(&s, input), out(&p, input));
    }
    assert_eq!(out(&s, "4800\n"), "600000 left of 604800\n");
}

#[test]
fn a_port_dependent_definition_is_run_stage() {
    let (p, s, _) = staged(UPTIME, BUILD_FUEL);
    let colors = color(p.unit());
    assert!(colors.contains(&("week".into(), Stage::Build)));
    // `main` is a function, so it is known at build; its body reads the port and stays.
    let main = term(&s, "main");
    assert!(main.contains("604800"), "{main}");
    assert!(main.contains("stdin"), "{main}");
}

#[test]
fn a_definition_nothing_reads_is_never_evaluated() {
    let src = format!("broken = 1 / 0;\nunused = broken + 1;\n{UPTIME}");
    let (p, s, report) = staged(&src, BUILD_FUEL);
    assert_eq!(report.unread, ["broken", "unused"]);
    assert!(report.left.is_empty());
    assert!(s.unit().defs.iter().all(|d| d.name != "broken"));
    assert_eq!(out(&s, "5\n"), out(&p, "5\n"));
}

#[test]
fn a_failure_atom_is_a_value_the_build_computes() {
    let src = "ratio = int(\"n/a\");\nmain(stdin: Lines) -> (stdout: Lines) {\n  \
               stdout <- String(ratio) else \"no ratio\";\n}\n";
    let (p, s, report) = staged(src, BUILD_FUEL);
    assert_eq!(report.built, ["ratio"]);
    assert_eq!(term(&s, "ratio"), "#invalid");
    assert_eq!(out(&s, "x\n"), "no ratio\n");
    assert_eq!(out(&s, "x\n"), out(&p, "x\n"));
}

#[test]
fn an_evaluation_error_is_left_to_run() {
    // An integer past the evaluator's size limit stops evaluation: the build leaves it, and
    // the run reports it in the ordinary way.
    let src = "huge = 10 ** 100000000;\nmain(stdin: Lines) -> (stdout: Lines) {\n  \
               stdout <- String(huge);\n}\n";
    let (p, s, report) = staged(src, BUILD_FUEL);
    assert!(report.built.is_empty());
    assert_eq!(report.left.len(), 1, "{:?}", report.left);
    assert_eq!(term(&s, "huge"), term(&p, "huge"));
    assert_eq!(out(&s, "x\n"), out(&p, "x\n"));
    assert!(out(&s, "x\n").starts_with("error: "), "{}", out(&s, "x\n"));
}

#[test]
fn a_term_out_of_fuel_is_left_to_run() {
    let src = "twice(positional n: int) = n + n;\nbig = twice(twice(twice(3)));\n\
               main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- String(big);\n}\n";
    let (p, s, report) = staged(src, 2);
    assert!(report.built.is_empty());
    assert_eq!(report.left.len(), 1, "{:?}", report.left);
    assert!(report.left[0].1.contains("fuel"), "{:?}", report.left);
    assert_eq!(out(&s, "x\n"), "24\n");
    assert_eq!(out(&p, "x\n"), "24\n");
    let (_, full, report) = staged(src, BUILD_FUEL);
    assert_eq!(report.built, ["big"]);
    assert_eq!(term(&full, "big"), "24");
}

#[test]
fn a_dead_branch_is_cut_at_build() {
    let src = "verbose = false;\nmain(stdin: Lines) -> (stdout: Lines) {\n  \
               line = stdin[1] else \"\";\n  \
               stdout <- if verbose { \"read: \" ++ line } else { line };\n}\n";
    let (p, s, _) = staged(src, BUILD_FUEL);
    let main = term(&s, "main");
    assert!(!main.contains("read: "), "{main}");
    assert_eq!(out(&s, "abc\n"), out(&p, "abc\n"));
}

#[test]
fn a_local_definition_is_computed_where_it_is_read() {
    // `k` is build-stage, so its reads are computed and its definition dropped; `inc`, a
    // function nothing reads, is never evaluated; `n` reads the port and stays.
    let src = "main(stdin: Lines) -> (stdout: Lines) {\n  k = 6 * 7;\n  \
               inc(y: int) = y + 1;\n  n = int(stdin[1]) else 0;\n  \
               stdout <- String(n + k);\n}\n";
    let (p, s, report) = staged(src, BUILD_FUEL);
    let main = term(&s, "main");
    assert!(main.contains("42"), "{main}");
    assert!(!main.contains('k') && !main.contains("inc"), "{main}");
    assert!(report.unread.contains(&"inc".to_string()), "{report:?}");
    assert_eq!(out(&s, "8\n"), "50\n");
    assert_eq!(out(&s, "8\n"), out(&p, "8\n"));
}

#[test]
fn a_write_of_a_constant_is_left_to_run() {
    // The text is build-stage; the write is an effect, so the build does not run it.
    let src = "main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- \"a\" ++ \"b\";\n}\n";
    let (p, s, report) = staged(src, BUILD_FUEL);
    assert_eq!(report.left, []);
    assert!(term(&s, "main").contains("\"ab\""), "{}", term(&s, "main"));
    assert_eq!(out(&s, "x\n"), "ab\n");
    assert_eq!(out(&s, "x\n"), out(&p, "x\n"));
}
