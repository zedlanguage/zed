//! `mix`: the build evaluates the demanded build-stage definitions and subterms, leaves the
//! port-dependent ones to run, and the staged program writes what the program writes.

use zedc::stage::{Stage, color};

use super::{out, staged, term};

/// A log filter: the day length and the cutoff are computed at build, the rest per line.
const UPTIME: &str = "day = 60 * 60 * 24;\nweek = 7 * day;\n\
    main(stdin: Lines) -> (stdout: Lines) {\n  \
    secs = int(stdin[1]) else 0;\n  \
    stdout <- String(week - secs) ++ \" left of \" ++ String(week);\n}\n";

#[test]
fn constants_are_computed_at_build() {
    let (p, s, report) = staged(UPTIME);
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
    let (p, s, _) = staged(UPTIME);
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
    let (p, s, report) = staged(&src);
    assert_eq!(report.unread, ["broken", "unused"]);
    assert!(report.left.is_empty());
    assert!(s.unit().defs.iter().all(|d| d.name != "broken"));
    assert_eq!(out(&s, "5\n"), out(&p, "5\n"));
}

#[test]
fn a_failure_atom_is_a_value_the_build_computes() {
    let src = "ratio = int(\"n/a\");\nmain(stdin: Lines) -> (stdout: Lines) {\n  \
               stdout <- String(ratio) else \"no ratio\";\n}\n";
    let (p, s, report) = staged(src);
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
    let (p, s, report) = staged(src);
    assert!(report.built.is_empty());
    assert_eq!(report.left.len(), 1, "{:?}", report.left);
    assert_eq!(term(&s, "huge"), term(&p, "huge"));
    assert_eq!(out(&s, "x\n"), out(&p, "x\n"));
    assert!(out(&s, "x\n").starts_with("error: "), "{}", out(&s, "x\n"));
}

#[test]
fn a_term_whose_form_shows_it_ends_is_built_with_no_fuel() {
    let src = "twice(positional n: int) = n + n;\nbig = twice(twice(twice(3)));\n\
               main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- String(big);\n}\n";
    let (p, s, report) = staged(src);
    assert_eq!(report.built, ["big"]);
    assert_eq!(term(&s, "big"), "24");
    assert_eq!(out(&s, "x\n"), out(&p, "x\n"));
    // A fold with an operator that ends, through a lambda bound by `let`, is built too.
    let src = "main(stdin: Lines) -> (stdout: Lines) {\n  add(a: int, b: int) = a + b;\n  \
               k = add(a: add(a: 1, b: 2), b: 3);\n  stdout <- String(k);\n}\n";
    let (_, s, report) = staged(src);
    assert!(report.left.is_empty(), "{:?}", report.left);
    assert!(
        term(&s, "main").contains("\"6\"") || term(&s, "main").contains('6'),
        "{}",
        term(&s, "main")
    );
}

#[test]
fn a_term_whose_form_does_not_show_it_ends_is_left_to_run() {
    // `w(w)` calls through a parameter: the build does not run it, whatever fuel it would
    // take, and the residual program keeps it as written.
    let src = "w(positional f) = f(f);\nspin = w(w);\n\
               main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- if false { String(spin) } else { \"x\" };\n}\n";
    let (_, s, report) = staged(src);
    assert!(report.built.is_empty(), "{:?}", report.built);
    assert_eq!(report.left.len(), 1, "{:?}", report.left);
    assert_eq!(report.left[0].1, "its form does not show that it ends");
    assert_eq!(term(&s, "spin"), "w(w)");
}

#[test]
fn the_form_rule_reads_calls_and_family_operators() {
    use zed_kernel::Term;
    use zed_kernel::term::build::{lam, lit, var};
    use zedc::stage::ends;
    let app = |f: Term, args: Vec<Term>| Term::App(std::sync::Arc::new(f), args);
    let lt = |x: &str, e: Term, b: Term| {
        Term::Let(x.into(), std::sync::Arc::new(e), std::sync::Arc::new(b))
    };
    // A lambda called directly, by a `let` name, or a prelude word ends.
    assert!(ends(&app(lam(&["x"], var("x")), vec![lit(1i64)])));
    assert!(ends(&lt(
        "f",
        lam(&["x"], var("x")),
        app(var("f"), vec![lit(1i64)])
    )));
    assert!(ends(&app(var("len"), vec![lit(1i64)])));
    // A call through a parameter does not, nor through a name bound to one.
    let w = lam(&["f"], app(var("f"), vec![var("f")]));
    assert!(!ends(&w), "its body calls a parameter");
    // A lambda bound by `let` and never called is not evaluated, so it may be one.
    assert!(ends(&lt("w", w.clone(), lit(1i64))));
    assert!(!ends(&lt("w", w.clone(), app(var("w"), vec![var("w")]))));
    assert!(!ends(&app(w.clone(), vec![w.clone()])));
    let g = lam(&["f"], lt("h", var("f"), app(var("h"), vec![lit(1i64)])));
    assert!(!ends(&g));
    // A `let` name shadowed by a parameter is the parameter.
    let shadow = lt(
        "f",
        lam(&["x"], var("x")),
        lam(&["f"], app(var("f"), vec![lit(1i64)])),
    );
    assert!(!ends(&shadow));
}

#[test]
fn a_dead_branch_is_cut_at_build() {
    let src = "verbose = false;\nmain(stdin: Lines) -> (stdout: Lines) {\n  \
               line = stdin[1] else \"\";\n  \
               stdout <- if verbose { \"read: \" ++ line } else { line };\n}\n";
    let (p, s, _) = staged(src);
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
    let (p, s, report) = staged(src);
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
    let (p, s, report) = staged(src);
    assert_eq!(report.left, []);
    assert!(term(&s, "main").contains("\"ab\""), "{}", term(&s, "main"));
    assert_eq!(out(&s, "x\n"), "ab\n");
    assert_eq!(out(&s, "x\n"), out(&p, "x\n"));
}
