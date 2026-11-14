//! The `cases` tool (`zed/grammar/cases.txt` and `leftrec.txt`, read by the reference parser):
//! each form of a case line, each way a case can fail, and the blocks of `leftrec.txt`.

use super::{Dir, design, spec_dir};
use zed_tools::cases;
use zed_tools::spec::Spec;

/// Runs `cases.txt` = `cases` and `leftrec.txt` = `leftrec` over the grammars of the spec.
fn run(name: &str, cases_txt: &str, leftrec: &str) -> (zed_tools::Outcome, String) {
    let dir = spec_dir(name, &design(""), "");
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let files = Dir::new(&format!("{name}_files"));
    files.write("cases.txt", cases_txt);
    files.write("leftrec.txt", leftrec);
    let mut out = String::new();
    (cases::run_files(&spec, &files.root(), &mut out), out)
}

/// The real cases, over the real grammars, all agree with the reference parser.
#[test]
fn the_real_cases_and_left_recursion_cases_all_pass() {
    let dir = spec_dir("real_cases", &design(""), "");
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let mut out = String::new();
    let grammar = format!("{}/zed/grammar", zed_tools::impl_root());
    let outcome = cases::run_files(&spec, &grammar, &mut out);
    assert_eq!(outcome, Ok(true), "{out}");
    // Every case passed, so the only lines besides the cases are the two counts.
    let counts: Vec<&str> = out
        .lines()
        .filter(|l| !l.starts_with("ok   ") && !l.starts_with("       got  "))
        .collect();
    assert_eq!(counts.len(), 2, "{counts:?}");
    assert!(counts[0].starts_with("cases ") && counts[0].ends_with(" wrong 0"));
    assert!(counts[1].starts_with("left-recursion cases ") && counts[1].ends_with(" wrong 0"));
}

/// Each form of a case: a ring after `@`, an empty ring, a line break written as `⏎`, a
/// comment and a blank line, and `ERROR` accepting any error.
#[test]
fn each_form_of_a_case_line_is_read() {
    let text = concat!(
        "# a comment\n",
        "\n",
        "Expr@1 ::: a + b ::: (a + b)\n",
        "Expr@ ::: a + b ::: (a + b)\n",
        "Expr ::: a +⏎b ::: (a + b)\n",
        "Expr ::: a + ::: ERROR\n",
    );
    let (outcome, out) = run("case_forms", text, "");
    assert!(out.starts_with("ok   Expr | a + b\n"), "{out}");
    assert!(out.contains("cases 4 wrong 0\n"), "{out}");
    assert!(out.contains("ok   Expr | a +\n       got  ERROR@"), "{out}");
    assert!(out.contains("left-recursion cases 0 wrong 0\n"), "{out}");
    assert_eq!(outcome, Ok(true), "{out}");
}

/// What a failure prints: the token it stopped at and what was expected; a lexer error; and an
/// error inside a string's hole, from the lexer or from the parser.
#[test]
fn each_way_a_case_fails_is_printed() {
    let cases_txt = concat!(
        "Expr ::: a + ::: x\n",
        "Expr ::: a ` b ::: x\n",
        "Expr ::: \"${a +}\" ::: x\n",
        "Expr ::: \"${`}\" ::: x\n",
    );
    let (outcome, out) = run("case_fails", cases_txt, "");
    assert_eq!(outcome, Ok(false), "{out}");
    let got: Vec<&str> = out
        .lines()
        .filter_map(|l| l.strip_prefix("       got  "))
        .collect();
    assert_eq!(got.len(), 4, "{out}");
    assert!(got[0].starts_with("ERROR@2 "), "{out}");
    assert!(
        got[1].starts_with("ERROR ") && !got[1].starts_with("ERROR@"),
        "{out}"
    );
    assert!(got[2].starts_with("ERROR in hole "), "{out}");
    assert!(got[3].starts_with("ERROR in hole "), "{out}");
    assert_eq!(out.matches("DIFF ").count(), 4, "{out}");
    assert!(out.contains("       want x\n"), "{out}");
}

/// A line that is not a case, and a ring that is not a number, stop the tool.
#[test]
fn a_line_that_is_not_a_case_is_refused() {
    let (outcome, _) = run("case_bad_line", "Expr ::: a\n", "");
    assert_eq!(
        outcome,
        Err("not START ::: TEXT ::: WANT: Expr ::: a".to_string())
    );
    let (outcome, _) = run("case_bad_ring", "Expr@x ::: a ::: a\n", "");
    assert_eq!(outcome, Err("not a ring: Expr@x ::: a ::: a".to_string()));
}

/// `leftrec.txt`: each `grammar` line starts a block with its own grammar and cases; a case
/// before any `grammar` line stops the tool; a block whose grammar does not read stops it too.
#[test]
fn each_block_of_leftrec_is_a_grammar_with_its_cases() {
    let leftrec = concat!(
        "# comment\n",
        "grammar one\n",
        "A = A 'x' L1\n",
        "  | 'x' L1\n",
        "A ::: x x ::: (x x)\n",
        "A ::: y ::: ERROR@0 'x'\n",
        "grammar two\n",
        "B = 'y' L1\n",
        "B ::: y ::: y\n",
        "B ::: x ::: y\n",
    );
    let (outcome, out) = run("leftrec_blocks", "", leftrec);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(out.starts_with("cases 0 wrong 0\n"), "{out}");
    assert!(out.contains("ok   A | x x\n"), "{out}");
    assert!(out.contains("ok   A | y\n"), "{out}");
    assert!(out.contains("DIFF B | x\n"), "{out}");
    assert!(out.ends_with("left-recursion cases 4 wrong 1\n"), "{out}");

    let (outcome, _) = run("leftrec_early", "", "A ::: x ::: x\n");
    assert_eq!(
        outcome,
        Err("leftrec.txt: a line before any grammar: A ::: x ::: x".to_string())
    );
    let (outcome, _) = run("leftrec_bad", "", "grammar g\nA = 'x L1\nA ::: x ::: x\n");
    assert!(outcome.is_err_and(|e| e.contains("an unclosed literal")));
}

/// A tool run with no `cases.txt` says which file is missing.
#[test]
fn a_missing_cases_file_is_named() {
    let dir = spec_dir("cases_missing", &design(""), "");
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let files = Dir::new("cases_missing_files");
    let mut out = String::new();
    let outcome = cases::run_files(&spec, &files.root(), &mut out);
    assert!(
        outcome.as_ref().is_err_and(|e| e.contains("cases.txt")),
        "{outcome:?}"
    );
}
