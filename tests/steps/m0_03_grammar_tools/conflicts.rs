//! The `conflicts` tool on small plans written the way `docs/plan_dag.md` is: which pairs of
//! items it lists at one level with which shared paths, which paths it lists across levels with
//! which items, what the tool prints and refuses, and the cost of both on a plan of many
//! strands.

use zed_tools::conflicts::{compute, render, run};

/// A plan whose table holds `rows`, each `(level, id, title, needs, paths)`, followed by one
/// more section.
fn plan(rows: &[(usize, &str, &str, &str, &str)]) -> String {
    let mut text = String::from(
        "# Plan DAG\n\nThis file lists the remaining work. It covers the TODO items.\n\n\
         ## Items by level\n\n| Level | Id | Title | Size | Hard | Needs | Paths |\n\
         |---|---|---|---|---|---|---|\n",
    );
    for (level, id, title, needs, paths) in rows {
        text.push_str(&format!(
            "| {level} | {id} | {title} | S | no | {needs} | {paths} |\n"
        ));
    }
    text.push_str("\n## Why each item waits\n\nThe reasons.\n");
    text
}

/// A checker directory, files in and under it, a file every step touches, a test folder, a done
/// item, a path with no `/` at its end, a glob, and needs that order some sharing pairs.
const ROWS: &[(usize, &str, &str, &str, &str)] = &[
    (
        0,
        "A",
        "The checker",
        "none",
        "`DESIGN.md`, `crates/zedc-check/src/check/`",
    ),
    (
        0,
        "B",
        "A checker rule",
        "none",
        "`crates/zedc-check/src/check/mod.rs`, `STATUS.md`, `tests/steps/x/`",
    ),
    (0, "C", "Done: a spec edit", "none", "`DESIGN.md`"),
    (
        0,
        "D",
        "A driver flag",
        "none",
        "`crates/zedc`, `tests/steps/*/scaling.rs`",
    ),
    (
        1,
        "E",
        "After the checker",
        "A",
        "`DESIGN.md`, `crates/zedc-check/src/check/mod.rs (new)`",
    ),
    (1, "F", "The checker crate", "C", "`crates/zedc-check/`"),
    (
        2,
        "G",
        "After E",
        "E",
        "`DESIGN.md`, `tests/steps/*/scaling.rs`, `STATUS.md`",
    ),
    (
        0,
        "H",
        "Another rule",
        "none",
        "`crates/zedc-check/src/check/mod.rs`, `DESIGN.md`, `docs/x.md`",
    ),
];

/// The rows and lines the tool writes for `ROWS`.
const SAME_ROWS: &str = "\
| 0 | A, B | `crates/zedc-check/src/check/mod.rs` |
| 0 | A, H | `DESIGN.md`, `crates/zedc-check/src/check/mod.rs` |
| 0 | B, H | `crates/zedc-check/src/check/mod.rs` |
| 1 | E, F | `crates/zedc-check/src/check/mod.rs` |
";
const CROSS_LINES: &str = "\
- `DESIGN.md`: level 0: A, H; level 1: E; level 2: G
- `crates/zedc-check/`: level 0: A, B, H; level 1: E, F
- `crates/zedc-check/src/check/`: level 0: A, B, H; level 1: E
- `crates/zedc-check/src/check/mod.rs`: level 0: B, H; level 1: E
";

#[test]
fn the_pairs_and_paths_follow_the_rule_of_the_plan() {
    // A and E share DESIGN.md and the checker at different levels, so they appear only in the
    // lines across levels, although E needs A. C is done, so DESIGN.md names A, E, G and H.
    // B's STATUS.md and test folder, D's `crates/zedc` (no `/`, so not a directory) and the glob
    // under tests/ match nothing, and docs/x.md has one item. F's directory holds A's directory
    // and both copies of mod.rs, so its line names every item but D and G.
    let text = plan(ROWS);
    let c = compute(&text).expect("a plan");
    let written = render(&c);
    assert!(written.contains("There are 4 pairs."), "{written}");
    assert!(written.contains("There are 4 lines."), "{written}");
    assert!(
        written.contains(&format!("|---|---|---|\n{SAME_ROWS}\n")),
        "{written}"
    );
    assert!(
        written.ends_with(&format!("\n\n{CROSS_LINES}\n")),
        "{written}"
    );
}

#[test]
fn a_row_whose_title_starts_with_done_in_any_form_is_done() {
    // The plan writes done rows as "Done: ...", and also as "Done by <agent> (<date>) ...",
    // "Done (<agent>, <date>) ..." and "Done in <commit> ...". Each is done, so none of them
    // shares DESIGN.md with the open row A, at one level or across levels.
    let rows: &[(usize, &str, &str, &str, &str)] = &[
        (0, "A", "The checker", "none", "`DESIGN.md`"),
        (
            0,
            "B",
            "Done by w (2026-11-18): a spec edit",
            "none",
            "`DESIGN.md`",
        ),
        (
            0,
            "C",
            "Done (w, 2026-11-18): a spec edit",
            "none",
            "`DESIGN.md`",
        ),
        (1, "D", "Done in 0123abcde: a spec edit", "B", "`DESIGN.md`"),
        (0, "E", "Documented later", "none", "`DESIGN.md`"),
    ];
    let written = render(&compute(&plan(rows)).expect("a plan"));
    assert!(written.contains("| 0 | A, E | `DESIGN.md` |"), "{written}");
    assert!(written.contains("There are 1 pairs."), "{written}");
    assert!(!written.contains("`DESIGN.md`: level"), "{written}");
}

#[test]
fn shared_paths_follow_the_earlier_row_s_order() {
    // H lists mod.rs before DESIGN.md, A the other way; A's row comes first, so its order holds.
    let text = plan(ROWS);
    let written = render(&compute(&text).expect("a plan"));
    assert!(written.contains("| 0 | A, H | `DESIGN.md`, `crates/zedc-check/src/check/mod.rs` |"));
}

#[test]
fn the_tool_prints_the_lists_and_writes_nothing() {
    // TOOL-plan-counts-after-rebase: the lists were sections of the file, which went stale at
    // every rebase; now they are printed from the table, and the file is left as it is.
    let text = plan(ROWS);
    let dir = zed_tests::step_helpers::scratch("conflicts-print");
    std::fs::create_dir_all(&dir).expect("a temporary directory");
    let path = dir.join("plan_dag.md");
    std::fs::write(&path, &text).expect("writing the plan");
    let mut out = String::new();
    assert_eq!(run(&[path.display().to_string()], &mut out), Ok(true));
    assert_eq!(out, render(&compute(&text).expect("a plan")));
    assert!(
        out.starts_with("## File conflicts at the same level\n"),
        "{out}"
    );
    assert!(out.contains(SAME_ROWS), "{out}");
    assert!(out.ends_with(&format!("\n\n{CROSS_LINES}\n")), "{out}");
    assert_eq!(std::fs::read_to_string(&path).expect("the plan"), text);
    std::fs::remove_file(&path).expect("removing the plan");
    std::fs::remove_dir(&dir).expect("removing the directory");
}

#[test]
fn a_plan_whose_table_fails_the_plan_check_stops_the_tool() {
    // E written at level 0, the level of A, which it needs.
    let mut rows = ROWS.to_vec();
    rows[4].0 = 0;
    let dir = zed_tests::step_helpers::scratch("conflicts");
    std::fs::create_dir_all(&dir).expect("a temporary directory");
    let path = dir.join("plan_dag.md");
    std::fs::write(&path, plan(&rows)).expect("writing the plan");
    let args = [path.display().to_string()];
    let why = run(&args, &mut String::new()).expect_err("a wrong level");
    assert!(why.contains("does not pass the plan check"), "{why}");
    assert!(why.contains("E is at level 0"), "{why}");
    // So does a file that still holds the count sentence, which `plan --fix` takes out.
    let old = plan(ROWS).replace(
        "remaining work. It covers",
        "remaining work. It has 8 items, 3 edges and 3 levels (0 to 2). It covers",
    );
    std::fs::write(&path, &old).expect("writing the plan");
    let why = run(&args, &mut String::new()).expect_err("the count sentence");
    assert!(
        why.contains("the first paragraph states the counts"),
        "{why}"
    );
    assert_eq!(std::fs::read_to_string(&path).expect("the plan"), old);
    std::fs::remove_file(&path).expect("removing the plan");
    std::fs::remove_dir(&dir).expect("removing the directory");
}

#[test]
fn this_repository_s_conflict_lists_are_printed() {
    let mut out = String::new();
    assert_eq!(run(&[], &mut out), Ok(true), "{out}");
    assert!(
        out.starts_with("## File conflicts at the same level\n"),
        "{out}"
    );
}

#[test]
fn an_unknown_option_is_refused() {
    // `--check` among them: there is nothing in the file to check.
    for option in ["--write", "--check"] {
        let why = run(&[option.to_string()], &mut String::new()).expect_err("an option");
        assert!(why.starts_with("usage: conflicts [PLAN_DAG.md]"), "{why}");
    }
}

/// A plan of `n` strands of four items at levels 0 to 3, each needing the one before it. Every
/// item of a strand lists the strand's directory, a file of its own in it, and a file it shares
/// with the other strand of its pair (strands 2t and 2t + 1): each strand's directory gives a
/// line across levels, and each pair of strands gives 4 pairs at one level and a line for the
/// shared file.
pub(super) fn strands(n: usize) -> String {
    let mut rows = Vec::new();
    for s in 0..n {
        for d in 0..4 {
            let needs = if d == 0 {
                "none".to_string()
            } else {
                format!("S{s}-{}", d - 1)
            };
            let paths = format!(
                "`crates/s{s}/`, `crates/s{s}/f{d}.rs`, `docs/pair{}.md`",
                s / 2
            );
            rows.push((d, format!("S{s}-{d}"), needs, paths));
        }
    }
    let refs: Vec<(usize, &str, &str, &str, &str)> = rows
        .iter()
        .map(|(d, id, needs, paths)| (*d, id.as_str(), "Work", needs.as_str(), paths.as_str()))
        .collect();
    plan(&refs)
}

/// What `bench::conflicts::conflicts_scale_with_the_number_of_items` checks at each size,
/// checked at small sizes.
#[test]
fn the_conflicts_of_many_strands_are_found_at_small_sizes() {
    for m in [2, 4, 10] {
        strands_conflicts_found(&strands(m), m);
    }
}

/// The plan `text` of [`strands`]`(m)` has its `2m` pairs at one level and `m + m / 2` lines
/// across levels, and renders.
pub(super) fn strands_conflicts_found(text: &str, m: usize) {
    let c = compute(text).expect("a plan");
    assert_eq!((c.same.len(), c.cross.len()), (2 * m, m + m / 2));
    assert!(!render(&c).is_empty());
}

#[test]
fn a_path_span_holding_a_remark_is_refused() {
    // A remark inside the backticks would be read as part of the path and match nothing.
    let mut rows = ROWS.to_vec();
    rows[7].4 = "`crates/zedc/src/opt/ (the L3.11 pass)`";
    let text = plan(&rows);
    let why = compute(&text).err().expect("a remark in a path");
    assert!(
        why.contains("the path `crates/zedc/src/opt/ (the L3.11 pass)` of H holds a space"),
        "{why}"
    );
}
