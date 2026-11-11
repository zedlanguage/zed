//! The `cite` tool on small specs and trees: a label or step id that DESIGN.md does not define
//! is reported with its file and line, a fixture listed as exempt and a graph dagview saved are
//! not read, and the plan DAG's steps to come are accepted. This file is itself one of the exempt fixtures.

use zed_tests::scaling::check;
use zed_tools::cite::{FIXTURES, PLAN, check_citations, run};

/// A DESIGN.md with the labels `order` and `checking_in_zed`, and the steps L1.1, L1.2 and
/// L1.2a, with `extra` at the end of its first section.
fn design(extra: &str) -> String {
    format!(
        "# (sec:overview) Part A\n\n## (sec:order) Order\n\nText.{extra}\n\n\
         ## (sec:checking_in_zed) Checking\n\nText.\n\n\
         ## (sec:steps) The steps, layer by layer\n\n### L1 — The core\n\n\
         L1.1. Parse the program.\nL1.2. Check it.\n**L1.2a.** Check it again.\n\n\
         # (sec:alternatives) Appendix\n"
    )
}

/// The tree of `files`, each `(path, text)`, with the exempt fixtures added.
fn tree(files: &[(&str, &str)]) -> Vec<(String, String)> {
    files
        .iter()
        .copied()
        .chain(FIXTURES.iter().map(|f| (*f, "sec:nosuch and L9.9")))
        .map(|(p, t)| (p.to_string(), t.to_string()))
        .collect()
}

/// What the tool prints for `files` against `design`, and whether it passed.
fn checked(design: &str, files: &[(&str, &str)]) -> (bool, String) {
    let mut out = String::new();
    let ok = check_citations(design, &tree(files), &mut out).expect("DESIGN.md has a plan");
    (ok, out)
}

#[test]
fn defined_labels_and_steps_pass() {
    let src = "//! The natural order (DESIGN.md sec:order, step L1.2a), and sec:checking_in_zed.\n\
               // Steps L1.1 and L1.2.";
    assert_eq!(
        checked(&design(""), &[("src/a.rs", src)]),
        (true, String::new())
    );
}

#[test]
fn an_undefined_label_is_reported_with_its_file_and_line() {
    let src = "fn f() {}\n/// The order of values (sec:keys).\n";
    assert_eq!(
        checked(&design(""), &[("src/a.rs", src)]),
        (
            false,
            "src/a.rs:2: sec:keys is no label of DESIGN.md\n".into()
        )
    );
}

#[test]
fn a_label_that_a_defined_one_begins_with_is_reported() {
    // The case of sec:checking, which only sec:checking_in_zed begins with.
    let (ok, out) = checked(&design(""), &[("STATUS.md", "see sec:checking.")]);
    assert!(!ok);
    assert_eq!(out, "STATUS.md:1: sec:checking is no label of DESIGN.md\n");
}

#[test]
fn an_undefined_step_is_reported() {
    let (ok, out) = checked(&design(""), &[("src/a.rs", "at step L1.3, then (L1.2b).")]);
    assert!(!ok);
    assert_eq!(
        out,
        "src/a.rs:1: L1.3 is no step of DESIGN.md\nsrc/a.rs:1: L1.2b is no step of DESIGN.md\n"
    );
}

#[test]
fn a_step_inside_a_longer_word_number_or_path_is_no_citation() {
    let src = "xL1.9 1.L1.9 L1.9b3 L1.90xy l01_09 nosec:keys";
    assert_eq!(
        checked(&design(""), &[("src/a.rs", src)]),
        (true, String::new())
    );
}

#[test]
fn design_md_is_checked_too() {
    let text = design(" See sec:keys and step L1.7.");
    let (ok, out) = checked(&text, &[("DESIGN.md", &text)]);
    assert!(!ok);
    assert_eq!(
        out,
        "DESIGN.md:5: sec:keys is no label of DESIGN.md\nDESIGN.md:5: L1.7 is no step of DESIGN.md\n"
    );
}

#[test]
fn a_step_a_plan_row_adds_to_design_is_accepted() {
    let plan = "| 3 | DESCENT-sum | Sum entry, building new DESIGN step L1.2c after L1.2b | S |\n\
                - **DESCENT-sum.** Consider splitting into L1.2d and L1.2e.\n";
    let design_text = design(" The sum entry arrives at step L1.2c.");
    let files = [(PLAN, plan), ("DESIGN.md", design_text.as_str())];
    assert_eq!(checked(&design_text, &files), (true, String::new()));
    // A step named only in the plan's notes, as L1.2d is, is not one to come.
    let (ok, out) = checked(&design(""), &[(PLAN, plan), ("src/a.rs", "step L1.2d")]);
    assert!(!ok);
    assert_eq!(out, "src/a.rs:1: L1.2d is no step of DESIGN.md\n");
}

#[test]
fn the_plan_s_labels_are_checked() {
    let (ok, out) = checked(&design(""), &[(PLAN, "| 0 | X | see sec:keys | S |\n")]);
    assert!(!ok);
    assert_eq!(
        out,
        "docs/plan_dag.md:1: sec:keys is no label of DESIGN.md\n"
    );
}

#[test]
fn a_graph_dagview_saved_is_not_read_but_dagview_s_source_is() {
    // A saved graph names items by the ids dagview showed that day, renamed steps included.
    let graph = r#"{"nodes":[{"id":"L14.1a"},{"id":"L1.9"}],"note":"sec:keys"}"#;
    let source = "// The layout of step L1.9 (sec:keys).\n";
    let (ok, out) = checked(
        &design(""),
        &[
            ("tools/dagview/live-graph-2026-11-11.json", graph),
            ("tools/dagview/layout.ts", source),
        ],
    );
    assert!(!ok);
    assert_eq!(
        out,
        "tools/dagview/layout.ts:1: sec:keys is no label of DESIGN.md\n\
         tools/dagview/layout.ts:1: L1.9 is no step of DESIGN.md\n"
    );
}

#[test]
fn an_exempt_path_that_is_not_tracked_is_reported() {
    let mut out = String::new();
    let files = vec![("src/a.rs".to_string(), "sec:order".to_string())];
    assert_eq!(check_citations(&design(""), &files, &mut out), Ok(false));
    assert!(
        out.contains("listed as exempt, but not a tracked file"),
        "{out}"
    );
}

#[test]
fn a_design_with_no_plan_stops_the_tool() {
    let mut out = String::new();
    assert!(check_citations("## (sec:order) Order\n", &tree(&[]), &mut out).is_err());
}

#[test]
fn this_repository_s_citations_are_defined() {
    let Some(spec) = zed_tests::spec::dir("the citations of DESIGN.md and this repository") else {
        return;
    };
    let mut out = String::new();
    let spec = spec.to_str().expect("UTF-8 path").to_string();
    assert_eq!(run(&[spec], &mut out), Ok(true), "{out}");
}

#[test]
fn cite_scales_with_the_number_of_citations() {
    let n = 2000;
    let line = "// sec:order at step L1.2a, sec:checking_in_zed at L1.1.\n";
    let texts = [line.repeat(n), line.repeat(8 * n)];
    let design = design("");
    let trees = texts.each_ref().map(|t| tree(&[("src/a.rs", t)]));
    check("cite, by citations", n, |m| {
        let mut out = String::new();
        let files = &trees[usize::from(m != n)];
        assert_eq!(check_citations(&design, files, &mut out), Ok(true));
    });
}
